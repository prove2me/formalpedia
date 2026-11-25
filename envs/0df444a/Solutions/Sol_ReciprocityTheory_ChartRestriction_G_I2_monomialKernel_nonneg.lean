-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.monomialKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:49.632977+00:00
-- url     : https://prove2.me/submissions/3004a0f0-6078-4568-b125-a375bb7f34e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialMass_pos

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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (z : EuclideanSpace ℂ (Fin g)) :
    0 ≤ fa1K p z := by
  unfold fa1K
  exact Finset.sum_nonneg fun α _ => div_nonneg (by positivity) (monomialMass_pos α).le
end ReciprocityTheory.ChartRestriction.G.I2
