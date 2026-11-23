-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.eval_eq_sum_coeff_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:43.138925+00:00
-- url     : https://prove2.me/submissions/2a24d3a0-c368-45f4-bed7-faec236ccde5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq

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
    MvPolynomial.eval (fun i => z i) p = ∑ α ∈ p.support, MvPolynomial.coeff α p * monomialOfMultiindex α z := by
  first
  | (simp [MvPolynomial.eval_eq', monomialOfMultiindex]; done)
  | (simp [MvPolynomial.eval_eq, monomialOfMultiindex, Finsupp.prod]; done)
  | (rw [MvPolynomial.eval_eq']; unfold monomialOfMultiindex; done)
end ReciprocityTheory.ChartRestriction.G.I2
