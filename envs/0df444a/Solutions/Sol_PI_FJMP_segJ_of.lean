-- Prove2me | solution 1 for PI.FJMP.segJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:19:08.478628+00:00
-- url     : https://prove2.me/submissions/406bfc81-7abf-48fa-9f12-b7085e494742

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_seg1
import Theorems.Thm_PI_FJMP_seg2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution (hW1 : FormWt1) (hW2 : FormWt2) (hR1 : FormRaise1) (hR2 : FormRaise2) : SegJ := by
  intro p q r s μ μ' P hM
  refine ⟨fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).1,
    fun i i' h => (seg1 hW1 hW2 hR1 hM (.inl i) (.inl i') h (fun c => ?_)).2,
    fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h (fun c => ?_)).1,
    fun j j' h => (seg1 hW1 hW2 hR1 hM (.inr j) (.inr j') h (fun c => ?_)).2,
    fun k k' h => (seg2 hW1 hW2 hR2 hM (.inl k) (.inl k') h (fun a => ?_)).1,
    fun k k' h => (seg2 hW1 hW2 hR2 hM (.inl k) (.inl k') h (fun a => ?_)).2,
    fun l l' h => (seg2 hW1 hW2 hR2 hM (.inr l) (.inr l') h (fun a => ?_)).1,
    fun l l' h => (seg2 hW1 hW2 hR2 hM (.inr l) (.inr l') h (fun a => ?_)).2⟩
  all_goals first
    | (rcases c with _ | _ <;> rfl)
    | (rcases a with _ | _ <;> rfl)
end PI.FJMP
