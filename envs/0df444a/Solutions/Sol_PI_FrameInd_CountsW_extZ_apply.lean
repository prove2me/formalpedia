-- Prove2me | solution 1 for PI.FrameInd.CountsW.extZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:57:37.01991+00:00
-- url     : https://prove2.me/submissions/e1a3234a-c681-4e7d-bc02-2fad9e87e707

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts

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
theorem _root_.solution {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ) (i : n) :
    extZ p y i = if h : p i then y ⟨i, h⟩ else 0 := rfl
end PI.FrameInd.CountsW
