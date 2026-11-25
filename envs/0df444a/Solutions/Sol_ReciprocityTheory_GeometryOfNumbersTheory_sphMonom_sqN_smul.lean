-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_sqN_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:12.429443+00:00
-- url     : https://prove2.me/submissions/b46de184-73ca-42e4-9c31-2249db5193bc

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA

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
theorem _root_.solution (c : ℂ) (z : Fin N → ℂ) : sqN (c • z) = ‖c‖ ^ 2 * sqN z := by
  simp only [sqN, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]
end ReciprocityTheory.GeometryOfNumbersTheory
