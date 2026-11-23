-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:43.72391+00:00
-- url     : https://prove2.me/submissions/ba7317be-ad13-4588-858d-912e7995284e

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
theorem _root_.solution (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    paIP q F F = ((∫ v, ‖F v‖ ^ 2 * paW q v : ℝ) : ℂ) := by
  unfold paIP
  rw [← integral_complex_ofReal]
  congr 1; funext v
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring
end ReciprocityTheory.ChartRestriction.G.I2
