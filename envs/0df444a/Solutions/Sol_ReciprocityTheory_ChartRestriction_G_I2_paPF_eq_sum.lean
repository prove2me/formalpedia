-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paPF_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:12:47.529651+00:00
-- url     : https://prove2.me/submissions/7d819e72-1cc5-4825-b97c-f8584d513e45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (p : MvPolynomial ι ℂ) :
    paPF p = ∑ m ∈ p.support, p.coeff m • paMono m := by
  funext v
  conv_lhs => rw [paPF, p.as_sum, map_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, paMono, paPF, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun m _ => by ring
end ReciprocityTheory.ChartRestriction.G.I2
