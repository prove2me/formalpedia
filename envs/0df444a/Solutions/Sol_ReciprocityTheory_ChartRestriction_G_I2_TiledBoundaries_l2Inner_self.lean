-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.l2Inner_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:03:34.146735+00:00
-- url     : https://prove2.me/submissions/e1361c7a-75f7-4a48-a642-41b07a308092

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) :
    X.l2ip q F F = (X.l2 q F : ℂ) := by
  unfold PT.l2ip PT.l2 PT.ptN2
  simp only [MeasureTheory.setAverage_eq]
  rw [Complex.real_smul, smul_eq_mul, Complex.ofReal_mul, ← integral_complex_ofReal]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
