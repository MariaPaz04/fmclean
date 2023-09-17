
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
  
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hp,
  by_contradiction hn,
  have hnp : ¬P := hn,
  contradiction,

end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro hp,
  by_contradiction hn,
  have hnp : ¬P := hn,
  contradiction,
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,

end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h,
  right,
  exact h,
  left,
  exact h,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h,
  split,
  exact h_right,
  exact h_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro p,
  cases h,
  have hp := h p,
  contradiction,
  exact h,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro fp,
  cases h,
  have hp := fp h,
  contradiction,
  exact h,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro fq,
  intro p,
  have hpq := pq p,
  have hfq := fq hpq,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro pq,
  intro p,
  by_contradiction fq,
  have fpq := pq fq,
  have ppq := fpq p,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro pq,
  intro fq,
  intro p,
  have hpq := pq p,
  have hfq := fq hpq,

  contradiction,
  intro pq,
  intro p,
  by_contradiction fq,
  have fpq := pq fq,
  have ppq := fpq p,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  apply h,
  by_cases p: P,
  left,
  exact p,
  right,
  exact p,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h1,
  intro h2,
  apply h2,
  apply h1,
  intro h3,
  have h4 := h2 h3,
  contradiction,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h1,
  intro h2,
  cases h1,
  cases h2,
  have h3 := h2_left h1,
  exact h3,
  cases h2,
  have h3 := h2_right h1,
  exact h3,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h1,
  intro h2,
  cases h1,
  cases h2,
  have h3 := h2 h1_left,
  exact h3,
  have h3 := h2 h1_right,
  exact h3,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro hp,
  apply h,
  left,
  exact hp,
  intro hq,
  apply h,
  right,
  exact hq,

end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h1,
  cases h1,
  intro h2,
  cases h2,
  have h3 := h1_left h2,
  exact h3,
  have h3 := h1_right h2,
  exact h3,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases hq: Q,
  right,
  intro hp,
  apply h,
  split,
  exact hp,
  exact hq,
  left,
  exact hq,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  intro h1,
  cases h1,
  cases h,
  have f := h h1_right,
  exact f,
  have f := h h1_left,
  exact f,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro h,
  by_cases hq: Q,
  right,
  intro hp,
  apply h,
  split,
  exact hp,
  exact hq,
  left,
  exact hq,
  intro h,
  intro h1,
  cases h1,
  cases h,
  have f := h h1_right,
  exact f,
  have f := h h1_left,
  exact f,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro h,
  split,
  intro hp,
  apply h,
  left,
  exact hp,
  intro hq,
  apply h,
  right,
  exact hq,
  intro h1,
  cases h1,
  intro h2,
  cases h2,
  have h3 := h1_left h2,
  exact h3,
  have h3 := h1_right h2,
  exact h3,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h,
  cases h_right,
  left,
  split,
  exact h_left,
  exact h_right,
  right,
  split,
  exact h_left,
  exact h_right,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h,
  cases h,
  split,
  exact h_left,
  left,
  exact h_right,
  cases h,
  split,
  exact h_left,
  right,
  exact h_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h,
  split,
  left,
  exact h,
  left,
  exact h,
  cases h,
  split,
  right,
  exact h_left,
  right,
  exact h_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h,
  cases h_left,
  left,
  exact h_left,
  cases h_right,
  left,
  exact h_right,
  right,
  split,exact h_left,
  exact h_right,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro p,
  intro q,
  apply h,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro h,
  intro pq,
  apply h,
  cases pq,
  exact pq_left,
  cases pq,
  exact pq_right,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h,
  exact h_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h,
  exact h_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro h,
  cases h,
  exact h_left,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p,
  cases p,
  exact p,
  exact p,
  intro p,
  left, 
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro h,
  intro j,
  cases j with u hu,
  have h1 := h u,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro h,
  by_contradiction fe,
  by_cases h1 : (∃x, ¬P x),
  have f1 := fe h1,
  exact f1,
  apply h,
  intro u,
  by_contradiction h2,
  apply h1,
  existsi u,
  exact h2,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro e,
  intro a,
  cases e with u hu,
  apply hu,
  apply a u,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro h,
  by_contradiction fe,
  by_cases h1 : (∃x, ¬P x),
  have f1 := fe h1,
  exact f1,
  apply h,
  intro u,
  by_contradiction h2,
  apply h1,
  existsi u,
  exact h2,
  intro e,
  intro a,
  cases e with u hu,
  apply hu,
  apply a u,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro h,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
  intro h,
  intro j,
  cases j with u hu,
  have h1 := h u,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro e,
  intro a,
  cases e with u hu,
  apply a u,
  exact hu,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro a,
  intro e,
  cases e with u hu,
  apply hu,
  apply a u,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro e,
  intro u,
  by_contradiction h,
  apply e,
  existsi u,
  exact h, 
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro a,
  by_contradiction h,
  have h2 : ∀x, ¬P x,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
  apply a,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro a,
  intro e,
  cases e with u hu,
  apply hu,
  apply a u,
  intro e,
  intro u,
  by_contradiction h,
  apply e,
  existsi u,
  exact h,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro e,
  intro a,
  cases e with u hu,
  apply a u,
  exact hu,
  intro a,
  by_contradiction h,
  have h2 : ∀x, ¬P x,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
  apply a,
  intro u,
  intro p,
  apply h,
  existsi u,
  exact p,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro e,
  cases e with u hu,
  cases hu,
  split,
  existsi u,
  exact hu_left,
  existsi u,
  exact hu_right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro e,
  cases e with u hu,
  cases hu,
  left,
  existsi u,
  exact hu,
  right,
  existsi u,
  exact hu,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro e,
  cases e,
  cases e with u hu,
  existsi u,
  left,
  exact hu,
  cases e with u hu,
  existsi u,
  right,
  exact hu,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
