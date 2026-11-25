-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericPieceRank_proof_7cb93377162e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:01.026331+00:00
-- url     : https://prove2.me/submissions/4924968c-8b2c-471e-81c3-514b81bc8237

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericPieceRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isLocalizedModule_genFibPiece_364fc6d1a2fe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericPieceRank
theorem _root_.solution : GenericPieceRank.Statement := by
  intro O _ _ _ K _ _ ι _ P _ m
  have := isLocalizedModule_genFibPiece P m
  rw [IsFractionRing.finrank_right_eq O (FractionRing O),
    IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := genFibPiece P m) (hp := le_rfl)]
end GenericPieceRank
end GroundTheory.Heights₂.Heights.NumbersDVR
