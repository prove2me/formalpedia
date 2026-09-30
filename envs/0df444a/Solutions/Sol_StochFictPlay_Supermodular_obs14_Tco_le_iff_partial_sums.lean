-- Prove2me | solution 1 for StochFictPlay.Supermodular.obs14_Tco_le_iff_partial_sums
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:35:37.169998+00:00
-- url     : https://prove2.me/submissions/58b3abde-6609-44b6-bd9d-fbea5b2ceeec

import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Mathlib.Tactic
open scoped BigOperators
open StochFictPlay.Supermodular

private theorem prefix_tail {m : ℕ} (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m))
    (i : Fin (m-1)) :
    (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) = Tco x i-Tco y i := by
  have hid : (∑ j : Fin m, if j.val < i.val+1 then y j-x j else 0) + (Tco y i-Tco x i) =
      (∑ j : Fin m, y j) - ∑ j : Fin m, x j := by
    simp only [Tco,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i.val < j.val
    · have hji : ¬j.val < i.val+1 := by omega
      simp [hij,hji]
    · have hji : j.val < i.val+1 := by omega
      simp [hij,hji]
  rw [hx.2,hy.2] at hid
  linarith

theorem solution (m : ℕ) (x y : Fin m → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin m)) (hy : y ∈ stdSimplex ℝ (Fin m)) :
    Tco x ≤ Tco y ↔
      ∀ k : ℕ, k < m → ∑ i : Fin m, (if i.val < k then y i - x i else 0) ≤ 0 := by
  constructor
  · intro h k hk
    by_cases hk0 : k=0
    · simp [hk0]
    · let i : Fin (m-1) := ⟨k-1,by omega⟩
      have hik : i.val+1=k := by dsimp [i]; omega
      have hh := prefix_tail x y hx hy i
      rw [hik] at hh
      rw [hh]
      exact sub_nonpos.mpr (h i)
  · intro h i
    have hi : i.val+1 < m := by have := i.isLt; omega
    have hh := h (i.val+1) hi
    rw [prefix_tail x y hx hy i] at hh
    exact sub_nonpos.mp hh
