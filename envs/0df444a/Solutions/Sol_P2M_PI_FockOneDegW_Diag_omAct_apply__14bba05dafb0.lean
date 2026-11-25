-- Prove2me | solution 1 for P2M_PI_FockOneDegW_Diag_omAct_apply__14bba05dafb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:14.825098+00:00
-- url     : https://prove2.me/submissions/94b7ebc3-e459-49aa-bcca-086bfd30988f

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution (p q r s : ℕ) (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) :
    omAct p q r s M = ∑ l, ∑ l', M l l' • omE l l' := by
  unfold FockH1Action.omAct
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]
end PI.FockOneDegW.Diag
