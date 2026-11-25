-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.wordsId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:22.963778+00:00
-- url     : https://prove2.me/submissions/c443f4c6-39fa-4a63-829a-bd5b9ed18a51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_dLR_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution : WordsId := by
  intro hL hR k p s ρ σ d ξ Z E _ _ F u v
  exact dLR_comp hL hR v F u
end PI.UnitaryGroupMassFormula.UsCost
