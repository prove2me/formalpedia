-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:31.583831+00:00
-- url     : https://prove2.me/submissions/d419387e-1fc4-4703-ae0a-e9a01eb19f11

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_volumeIoiPow_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (m k : ℕ) :
    ∫ r : Ioi (0 : ℝ), r.1 ^ k * Real.exp (-(r.1 ^ 2)) ∂(Measure.volumeIoiPow m) =
      Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) / 2 := by
  have hv := sphMonom_volumeIoiPow_integral m (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)))
  rw [hv]
  have hq : (-1 : ℝ) < ((m + k : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((m + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have h2 := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((m + k : ℕ) : ℝ)) (by norm_num) hq
  calc ∫ r in Ioi (0 : ℝ), r ^ m * (r ^ k * Real.exp (-(r ^ 2)))
      = ∫ x in Ioi (0 : ℝ), x ^ (((m + k : ℕ) : ℝ)) * Real.exp (-x ^ (2 : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        simp only [Real.rpow_natCast, Real.rpow_two]
        ring
    _ = 1 / 2 * Real.Gamma ((((m + k : ℕ) : ℝ) + 1) / 2) := h2
    _ = _ := by ring
end ReciprocityTheory.GeometryOfNumbersTheory
