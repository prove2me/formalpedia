-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.mask_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:51.0741+00:00
-- url     : https://prove2.me/submissions/7c71e67f-7c49-484b-8b0b-4b73f054e253

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_Gy_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_cross_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {y : Matrix (Fin r) (Fin r) ℂ} (h : Ok p0 y) (t : ℝ) (s : ℂ) (hs : conj s * s = 1 - (t : ℂ) ^ 2) :
    diagonal (sv p0) * Gy p0 (mask p0 t y) = diagonal (sv p0) * Gy p0 y + (Wm p0 s y)ᴴ * Wm p0 s y := by
  ext a b
  rw [Matrix.add_apply, Matrix.diagonal_mul, Matrix.diagonal_mul, Gy_apply, Gy_apply, Matrix.mul_apply]
  by_cases hab : ((a : ℕ) < p0 ↔ (b : ℕ) < p0)
  · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [mask, Wm, Matrix.of_apply, Matrix.conjTranspose_apply]
    by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
      simp [hk, ha, hb, sv] at hab ⊢ <;>
      first | ring1 | linear_combination (-(y k a * (starRingEnd ℂ) (y k b))) * hs
  · have hz := cross_zero h hab
    rw [Gy_apply] at hz
    rw [hz, mul_zero, zero_add]
    have hw : ∀ k : Fin r, star (Wm p0 s y k a) * Wm p0 s y k b = 0 := by
      intro k
      simp only [Wm, Matrix.of_apply]
      by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
        simp [hk, ha, hb] at hab ⊢
    simp only [Matrix.conjTranspose_apply, hw, Finset.sum_const_zero]
    have h4 : sv p0 a * ∑ k, mask p0 t y k a * sv p0 k * conj (mask p0 t y k b) =
        (t : ℂ) * (sv p0 a * ∑ k, y k a * sv p0 k * conj (y k b)) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [mask, Matrix.of_apply]
      by_cases hk : (k : ℕ) < p0 <;> by_cases ha : (a : ℕ) < p0 <;> by_cases hb : (b : ℕ) < p0 <;>
        simp [hk, ha, hb] at hab ⊢ <;> ring
    rw [h4, hz, mul_zero, mul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
