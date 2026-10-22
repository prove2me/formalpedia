-- Prove2me | solution 2 for RegLearnGames.FirstOrder.social_cost_eq_sum_inner
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:12:01.684138+00:00
-- url     : https://prove2.me/submissions/71c08c58-2320-42ef-9013-32f475536a2b

import Mathlib
import Definitions.Def_RegLearnGames_FirstOrder_Setting
set_option autoImplicit false

open Finset RegLearnGames.FirstOrder

lemma oo_pp_update {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (a : Fin d)
    (s : Fin n → Fin d) :
    AGT.profileProb (Function.update w i (Pi.single a 1)) s
      = (if s i = a then 1 else 0) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]
  congr 1
  · simp [Pi.single_apply]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma oo_pp {n d : ℕ} (w : Fin n → Fin d → ℝ) (i : Fin n) (s : Fin n → Fin d) :
    AGT.profileProb w s = w i (s i) * ∏ j ∈ univ.erase i, w j (s j) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ i)]

lemma oo_one {n d : ℕ} (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) :
    socialCost c w = ∑ i, (w i) ⬝ᵥ (costVec c w i) := by
  unfold socialCost socialCostPure
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold costVec AGT.expectedPayoff dotProduct
  simp only [oo_pp_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [oo_pp w i s]
  have : ∀ a : Fin d, w i a * (((if s i = a then 1 else 0) * ∏ j ∈ univ.erase i, w j (s j)) * c i s)
      = if s i = a then w i (s i) * (∏ j ∈ univ.erase i, w j (s j)) * c i s else 0 := by
    intro a
    by_cases h : s i = a
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem solution {n d : ℕ}
    (c : Fin n → (Fin n → Fin d) → ℝ)
    (w : ℕ → Fin n → Fin d → ℝ) (T : ℕ)
    (hw : ∀ t ∈ Finset.Icc 1 T, AGT.IsMixedProfile (w t)) :
    (∑ t ∈ Finset.Icc 1 T, socialCost c (w t)) =
      ∑ t ∈ Finset.Icc 1 T, ∑ i, (w t i) ⬝ᵥ (costVec c (w t) i) := by
  apply Finset.sum_congr rfl
  intro t _
  exact oo_one c (w t)
