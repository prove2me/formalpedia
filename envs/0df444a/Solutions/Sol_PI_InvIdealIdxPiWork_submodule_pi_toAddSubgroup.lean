-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.submodule_pi_toAddSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:11.58066+00:00
-- url     : https://prove2.me/submissions/e71b0694-acdd-4e9d-b2b5-263ce73ad7ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvIdealIdxPi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvertibleIdealIndex_SubmodulePiToAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvIdealIdxPiWork
open NumberField nonZeroDivisors
namespace PI.InvIdealIdxPiWork
theorem _root_.solution {ι : Type} {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ι → Submodule R M) :
    (Submodule.pi Set.univ p).toAddSubgroup =
      AddSubgroup.pi Set.univ (fun i => (p i).toAddSubgroup) := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_pi, AddSubgroup.mem_pi]
end PI.InvIdealIdxPiWork
