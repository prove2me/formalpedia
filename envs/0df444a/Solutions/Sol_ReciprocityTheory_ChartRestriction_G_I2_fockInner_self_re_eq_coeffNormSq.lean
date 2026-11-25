-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fockInner_self_re_eq_coeffNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:54:35.659372+00:00
-- url     : https://prove2.me/submissions/286173e7-83cc-4da9-b1fd-2f1055662c66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_mul_conj_gaussian_eq_coeffNormSq


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
theorem _root_.solution {g : ℕ} (p : MvPolynomial (Fin g) ℂ) (F : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : ∀ z, F z = MvPolynomial.eval (fun i => z i) p) : (fockIP F F).re = fa1N p := by
  unfold fockIP
  rw [integral_mul_conj_gaussian_eq_coeffNormSq p F hF, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.G.I2
