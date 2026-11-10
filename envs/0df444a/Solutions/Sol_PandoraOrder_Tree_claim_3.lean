-- Prove2me | solution 1 for PandoraOrder.Tree.claim_3
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:08:38.184368+00:00
-- url     : https://prove2.me/submissions/a23e8af1-765e-4d22-aebf-e9e3d57bf5ec

import Definitions.Def_PandoraOrder_Tree_Contracts

open PandoraOrder.Tree

@[reducible] noncomputable def instClaim3 : Instance 1 where
  size _ := 1
  law _ := ⟨fun _ => 1, fun _ => by norm_num, by simp⟩
  reward _ _ := 0
  reward_nonneg _ _ := le_rfl
  cost _ := 1
  cost_nonneg _ := zero_le_one

private lemma classicalReservation_instClaim3 :
    classicalReservation instClaim3 0 = -1 := by
  unfold classicalReservation
  have hset : {z : ℝ | (∑ a : Fin (instClaim3.size 0), (instClaim3.law 0).prob a *
      max (instClaim3.reward 0 a - z) 0) = instClaim3.cost 0} = {-1} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [Fin.sum_univ_one]
    change (1 : ℝ) * max (0 - z) 0 = 1 ↔ z = -1
    rw [one_mul, zero_sub]
    constructor
    · intro hz
      rcases le_total (-z) 0 with hle | hge
      · rw [max_eq_right hle] at hz
        norm_num at hz
      · rw [max_eq_left hge] at hz
        linarith
    · rintro rfl
      norm_num
  rw [hset, csInf_singleton]

theorem solution : ¬ (∀ {n : ℕ} (I : Instance n) (L : List (Fin n)) (_hL : L.Nodup)
    (i : ℕ) (_hi : i < L.length),
    (∀ E : List (Fin n), (L ++ E).Nodup →
      threshold I (L.drop i) ≤ threshold I ((L ++ E).drop i)) ∧
    (threshold I (L.drop i) =
      threshold I ((L.drop i).take (prefixLength I (L.drop i)))) ∧
    (prefixLength I (L.drop i) = 1 →
      threshold I (L.drop i) = classicalReservation I L[i]) ∧
    ((∀ j : ℕ, i < j → j < L.length →
      threshold I (L.drop i) < threshold I (L.drop j)) →
      ∀ y : ℝ, 0 ≤ y → y ≤ threshold I (L.drop i) →
      ∀ ω : (b : Fin n) → Fin (I.size b), outcomeWeight I ω ≠ 0 →
        auxiliaryStop I (L.drop i) (threshold I (L.drop i)) (fun b => I.reward b (ω b)) =
        auxiliaryStop I (L.drop i) y (fun b => I.reward b (ω b)))) := by
  intro h
  have hL : ([0] : List (Fin 1)).Nodup := by decide
  have hi : 0 < ([0] : List (Fin 1)).length := by decide
  have h3 := (h instClaim3 [0] hL 0 hi).2.2.1
  have hpref : prefixLength instClaim3 ([0].drop 0) = 1 := by
    unfold prefixLength
    simp
  have heq := h3 hpref
  simp only [List.drop_zero, List.getElem_cons_zero] at heq
  rw [classicalReservation_instClaim3] at heq
  have hnonneg : 0 ≤ threshold instClaim3 [0] :=
    Real.sInf_nonneg fun x hx => hx.1
  linarith
