-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.dLR_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:22.280887+00:00
-- url     : https://prove2.me/submissions/bfb4fff1-c6ab-40b6-8ba0-9b168f8685bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_dw_scale_at
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_map_lsz_LR
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_map_scx_LR

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
    (u v : List (B.Mat k r)) (f : B.Mat k r → E) (g : B.Mat k r) :
    B.dLR u v f g = ((((u ++ v).map lsz).prod : ℝ) : ℂ) • B.dLR (u.map sc) (v.map sc) f g := by
  rw [P.BetaSesquilinearity.dLR_eq, P.BetaSesquilinearity.dLR_eq, dw_scale_at (P.BetaSesquilinearity.wL u ++ P.BetaSesquilinearity.wR v), map_lsz_LR, map_scx_LR]
end PI.UnitaryGroupMassFormula.UsCost
