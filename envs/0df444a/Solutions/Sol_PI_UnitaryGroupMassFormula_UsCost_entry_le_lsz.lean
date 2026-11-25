-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.entry_le_lsz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:21.474569+00:00
-- url     : https://prove2.me/submissions/22f55fc4-6eb3-4ca8-9be5-ff2ef255d05b

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
theorem _root_.solution {k r : ℕ} (X : B.Mat k r) (a b : Fin (2 * r + k + 1)) : ‖X a b‖ ≤ lsz X := by
  calc ‖X a b‖ = ‖(Matrix.of.symm X) a b‖ := rfl
    _ ≤ ‖(Matrix.of.symm X) a‖ := norm_le_pi_norm _ b
    _ ≤ ‖Matrix.of.symm X‖ := norm_le_pi_norm _ a
    _ ≤ lsz X := le_max_right _ _
end PI.UnitaryGroupMassFormula.UsCost
