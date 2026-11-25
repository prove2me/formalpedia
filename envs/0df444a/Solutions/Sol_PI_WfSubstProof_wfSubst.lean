-- Prove2me | solution 1 for PI.WfSubstProof.wfSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:39:38.049962+00:00
-- url     : https://prove2.me/submissions/fc6d540c-e25b-406d-b931-a8000f166bb9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittSubstitution_CoeffMapMem
import Theorems.Thm_PI_WfSubstProof_substSub
import Theorems.Thm_PI_ExpIntWProof_mem_Wf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfSubstProof
namespace PI.WfSubstProof
theorem _root_.solution : PI.WfSubst := by
  intro p _ σ f a hf ha ha0 n
  have h := substSub ℂ_[p] (ExpIntWProof.Wf p) σ f a (fun m => ExpIntWProof.mem_Wf.2 (hf _))
    (fun m => ExpIntWProof.mem_Wf.2 (ha m)) ha0
  exact ExpIntWProof.mem_Wf.1 (h n)
end PI.WfSubstProof
