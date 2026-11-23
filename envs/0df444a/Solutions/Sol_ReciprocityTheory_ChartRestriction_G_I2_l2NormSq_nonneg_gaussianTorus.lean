-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.l2NormSq_nonneg_gaussianTorus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:38.782545+00:00
-- url     : https://prove2.me/submissions/13ec9bee-8bea-4af0-a33e-28cf9d5c4c2e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormSqNonnegGaussianTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) : 0 ≤ X.l2 q F := by
  unfold PT.l2
  rw [MeasureTheory.setAverage_eq]
  exact smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (MeasureTheory.integral_nonneg fun v => by unfold PT.ptN2; positivity)
end ReciprocityTheory.ChartRestriction.G.I2
