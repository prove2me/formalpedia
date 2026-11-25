-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.sphMonom_monoC_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:02:05.256563+00:00
-- url     : https://prove2.me/submissions/5a128918-398d-4a6d-838a-2725fd1b3c1d

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
theorem _root_.solution (a : Fin N → ℕ) (r : ℝ) (z : Fin N → ℂ) :
    monoC a (r • z) = (r : ℂ) ^ (∑ i, a i) * monoC a z := by
  simp only [monoC, Pi.smul_apply, Complex.real_smul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
end ReciprocityTheory.GeometryOfNumbersTheory
