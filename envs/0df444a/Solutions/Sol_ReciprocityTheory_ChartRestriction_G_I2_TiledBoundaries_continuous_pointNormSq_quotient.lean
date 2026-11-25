-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.continuous_pointNormSq_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:07.765404+00:00
-- url     : https://prove2.me/submissions/baf4c1ce-abf2-4d08-b1d3-157dc8a4eb7d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_cont_HC
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
theorem _root_.solution (X : PT E) (q : ℕ) {n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : Continuous F) :
    Continuous (X.ptN2 q F) := by
  unfold PT.ptN2
  exact (hF.norm.pow 2).mul (Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_re.comp cont_HC)))
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
