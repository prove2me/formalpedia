-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.dw_scale_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:09.369488+00:00
-- url     : https://prove2.me/submissions/68afbe87-0e0b-4d21-b333-9e3c51089dac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_dw_scale

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
theorem _root_.solution {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : List (Bool × B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    P.BetaSesquilinearity.Dw w f g = (((w.map (fun x => lsz x.2)).prod : ℝ) : ℂ) • P.BetaSesquilinearity.Dw (w.map scx) f g := congrFun (dw_scale w f) g
end PI.UnitaryGroupMassFormula.UsCost
