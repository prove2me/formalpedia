-- Prove2me | solution 1 for PI.FrameInd.CountsW.extZ_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:28.764748+00:00
-- url     : https://prove2.me/submissions/72710d16-fcdb-4d91-be7b-83bac004a8a7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts
import Theorems.Thm_PI_FrameInd_CountsW_extZ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd
namespace PI.FrameInd.CountsW
theorem _root_.solution {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ)
    (hy : extZ p y = 0) : y = 0 := by
  funext ⟨i, h⟩
  have h1 := congrFun hy i
  simpa [extZ_apply, h] using h1
end PI.FrameInd.CountsW
