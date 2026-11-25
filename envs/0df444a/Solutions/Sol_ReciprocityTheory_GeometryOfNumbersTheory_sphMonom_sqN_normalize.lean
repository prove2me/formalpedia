-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_normalize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:15.485888+00:00
-- url     : https://prove2.me/submissions/60b087d5-af5a-47fb-8161-aebf3f204164

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_nonneg
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_sphMonom_sqN_smul

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
variable {N : ℕ}
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (z : Fin N → ℂ) (hz : z ≠ 0) :
    sqN ((((Real.sqrt (sqN z))⁻¹ : ℝ) : ℂ) • z) = 1 := by
  have hs : sqN z ≠ 0 := by
    intro h
    apply hz
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖z j‖)).1 h i (Finset.mem_univ i)
    simpa using this
  rw [sphMonom_sqN_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (sphMonom_sqN_nonneg z), inv_mul_cancel₀ hs]
end ReciprocityTheory.GeometryOfNumbersTheory
