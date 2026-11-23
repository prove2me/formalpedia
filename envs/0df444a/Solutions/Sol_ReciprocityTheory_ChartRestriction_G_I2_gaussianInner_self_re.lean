-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_self_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:03.464338+00:00
-- url     : https://prove2.me/submissions/fab57ebe-3fd5-43c0-bd8c-cf8a189d7e52

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paW_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gaussianInner_self

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
    paIP q F F = ((paIP q F F).re : ℂ) ∧ 0 ≤ (paIP q F F).re := by
  rw [gaussianInner_self, Complex.ofReal_re]
  exact ⟨rfl, integral_nonneg fun v => by have := paW_pos q v; positivity⟩
end ReciprocityTheory.ChartRestriction.G.I2
