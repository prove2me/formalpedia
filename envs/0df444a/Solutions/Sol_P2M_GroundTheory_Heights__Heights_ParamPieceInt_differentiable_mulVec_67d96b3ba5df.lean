-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ParamPieceInt_differentiable_mulVec_67d96b3ba5df
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:17.69406+00:00
-- url     : https://prove2.me/submissions/084e4a17-9295-4a38-978f-5859e5bf8493

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamPieceInt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamPieceInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ParamPieceInt
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ParamPieceInt
theorem _root_.solution (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
  have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
  convert h using 1
  funext x
  simp
end GroundTheory.Heights₂.Heights.ParamPieceInt
