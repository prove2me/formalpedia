-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fa1Mono_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:42.22966+00:00
-- url     : https://prove2.me/submissions/3b085d70-8f75-4717-af08-defc84797a0c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) (r : ℝ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (r • z) = (r : ℂ) ^ (∑ i, α i) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul, mul_pow]
end ReciprocityTheory.ChartRestriction.G.I2
