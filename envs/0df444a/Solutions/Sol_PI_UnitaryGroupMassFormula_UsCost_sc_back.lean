-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.sc_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:59:50.626258+00:00
-- url     : https://prove2.me/submissions/fdb60290-0301-4b30-9a27-5984952d73f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_EntryLeLsz
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_lsz_pos

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
theorem _root_.solution {k r : ℕ} (X : B.Mat k r) : ((lsz X : ℝ) : ℂ) • sc X = X := by
  unfold sc
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (lsz_pos X).ne', Complex.ofReal_one, one_smul]
end PI.UnitaryGroupMassFormula.UsCost
