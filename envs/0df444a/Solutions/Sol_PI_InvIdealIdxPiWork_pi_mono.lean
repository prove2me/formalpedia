-- Prove2me | solution 1 for PI.InvIdealIdxPiWork.pi_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:00.306327+00:00
-- url     : https://prove2.me/submissions/2e20001c-df93-46fb-a2af-9981b34f37b0

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
theorem _root_.solution {ι : Type} {G : Type*} [AddGroup G] {A B : ι → AddSubgroup G}
    (h : ∀ i, A i ≤ B i) : AddSubgroup.pi Set.univ A ≤ AddSubgroup.pi Set.univ B := by
  intro x hx
  rw [AddSubgroup.mem_pi] at hx ⊢
  exact fun i hi => h i (hx i hi)
end PI.InvIdealIdxPiWork
