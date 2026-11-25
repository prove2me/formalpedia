-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.paMono_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:12:19.628158+00:00
-- url     : https://prove2.me/submissions/ec993a09-09f0-494d-9e35-988a3bf2e922

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
theorem _root_.solution (α : ι →₀ ℕ) (v : EuclideanSpace ℂ ι) : ‖paMono α v‖ ≤ ‖v‖ ^ α.degree := by
  simp only [paMono, paPF, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, norm_prod, norm_pow]
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun i _ => by positivity)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le v i) _)
end ReciprocityTheory.ChartRestriction.G.I2
