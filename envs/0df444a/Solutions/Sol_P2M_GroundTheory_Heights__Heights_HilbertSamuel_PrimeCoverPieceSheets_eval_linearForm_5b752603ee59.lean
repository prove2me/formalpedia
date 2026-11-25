-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PrimeCoverPieceSheets_eval_linearForm_5b752603ee59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:18.22966+00:00
-- url     : https://prove2.me/submissions/f25f6c20-4fa2-40f1-b4b5-66e7d1849fa6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPrimeCoverPieceSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscrAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFunctionFieldDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPrimeCoverPieceSheets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
theorem _root_.solution {n : ℕ} (c x : Fin n → ℂ) :
    eval x (ComplexSets.sum₂ c) = ∑ j, c j * x j := by
  simp [ComplexSets.sum₂]
end GroundTheory.Heights₂.Heights.HilbertSamuel.PrimeCoverPieceSheets
