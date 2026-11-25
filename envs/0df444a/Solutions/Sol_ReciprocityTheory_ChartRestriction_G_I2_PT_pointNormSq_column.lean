-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.pointNormSq_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:23.056038+00:00
-- url     : https://prove2.me/submissions/67ff00ee-d8d5-4f4c-ad21-3a24bfa6653c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_HC_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_self_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution (s : (Fin 1 → Vsp X.dim) → ℂ) (a : Vsp X.dim) :
    X.ptN2 1 s (fun _ => a) = X.toGT.ptN2 1 (X.col1 s) a := by
  simp only [PT.ptN2, GT.ptN2, PT.col1, HC_one, Hf_self_re]
end ReciprocityTheory.ChartRestriction.G.I2.PT
