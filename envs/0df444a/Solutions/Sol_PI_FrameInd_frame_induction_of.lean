-- Prove2me | solution 1 for PI.FrameInd.frame_induction_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:20.377346+00:00
-- url     : https://prove2.me/submissions/1d40e50f-fccd-4844-b9fd-62aad46e6528

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FinrankUperpOfDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_FrameInductionOf
import Theorems.Thm_PI_FrameInd_det_ne
import Theorems.Thm_PI_FrameInd_finrank_Uperp_of_det
import Theorems.Thm_PI_FrameInd_indep_of_det


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
open PI PI.FrameInd
namespace PI.FrameInd
theorem _root_.solution (hS : SignStep) (hU : UPos) : GramIndependentSignature := by
  intro k r z z' γ hs hp
  have hdet := det_ne k r z z' γ hs hp
  have hQ := hS k r z z' γ hs hp hdet
  exact ⟨indep_of_det k r z z' γ hdet, hQ, hU k r z z' γ hs hp hdet hQ,
    finrank_Uperp_of_det k r z z' γ hdet⟩
end PI.FrameInd
