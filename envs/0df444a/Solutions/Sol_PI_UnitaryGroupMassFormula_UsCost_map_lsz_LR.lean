-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.map_lsz_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:40.027124+00:00
-- url     : https://prove2.me/submissions/cf6e8b1a-4862-4619-a595-35051df81826

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution {k r : ℕ} (u v : List (B.Mat k r)) :
    (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v).map (fun x => lsz x.2) = (u ++ v).map lsz := by
  simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR, List.map_map, Function.comp_def]
end PI.UnitaryGroupMassFormula.UsCost
