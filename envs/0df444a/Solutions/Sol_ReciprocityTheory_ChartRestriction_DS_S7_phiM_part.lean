-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phiM_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:21:51.656263+00:00
-- url     : https://prove2.me/submissions/cdfd94d9-c0f1-4604-9d85-09770f6d2fdb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_fderiv_phiM_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_fderiv_phiM_upper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) {z B : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    fderiv ℂ (PhiM μ) z (B * z + z * B) =
      fderiv ℂ (PhiM μ) z (z * lowMinusUp B - lowMinusUp B * z) -
        2 * (∑ a, (μ a : ℂ) * B a a) * PhiM μ z := by
  set X1 : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun a b => if b < a then 2 * B a b else if a = b then B a b else 0 with hX1
  set X2 : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of fun a b => if a < b then 2 * B a b else if a = b then B a b else 0 with hX2
  have e1 : B + lowMinusUp B = X1 := by
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [lowMinusUp, hX1, h, lt_asymm h, ne_of_lt h] <;> ring
    · simp [lowMinusUp, hX1]
    · simp [lowMinusUp, hX1, h, lt_asymm h, (ne_of_lt h).symm] <;> ring
  have e2 : B - lowMinusUp B = X2 := by
    ext a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [lowMinusUp, hX2, h, lt_asymm h, ne_of_lt h] <;> ring
    · simp [lowMinusUp, hX2]
    · simp [lowMinusUp, hX2, h, lt_asymm h, (ne_of_lt h).symm] <;> ring
  have hL : IsLowerTri X1 := fun a b hab => by simp [hX1, lt_asymm hab, ne_of_lt hab]
  have hU : IsUpperTri X2 := fun a b hab => by simp [hX2, lt_asymm hab, (ne_of_lt hab).symm]
  have hsplit : B * z + z * B = (z * lowMinusUp B - lowMinusUp B * z) + (X1 * z + z * X2) := by
    rw [← e1, ← e2, Matrix.add_mul, Matrix.mul_sub]
    abel
  have d1 : ∑ a, (μ a : ℂ) * X1 a a = ∑ a, (μ a : ℂ) * B a a := by simp [hX1]
  have d2 : ∑ a, (μ a : ℂ) * X2 a a = ∑ a, (μ a : ℂ) * B a a := by simp [hX2]
  rw [hsplit, map_add, map_add, fderiv_phiM_lower μ hz hL, fderiv_phiM_upper μ hz hU, d1, d2]
  ring
end ReciprocityTheory.ChartRestriction.DS.S7
