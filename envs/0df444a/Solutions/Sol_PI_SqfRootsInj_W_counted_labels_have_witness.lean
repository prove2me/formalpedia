-- Prove2me | solution 1 for PI.SqfRootsInj.W.counted_labels_have_witness
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:44:04.667609+00:00
-- url     : https://prove2.me/submissions/0baa5b95-ee62-4569-9eb4-7386eb8de337

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Theorems.Thm_PI_SqfRootsInj_W_caseB_of
import Theorems.Thm_PI_SqfRootsInj_W_caseA_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution : Witness := by
  intro g r _ f hf
  obtain ⟨hlab, -, hnot⟩ := hf
  push Not at hnot
  obtain ⟨ℓ, hℓ, hBB, x, hx, y, hy, hp, hxy⟩ := hnot
  refine ⟨ℓ, hℓ, hBB, ?_⟩
  by_cases heq : minpoly (ZMod g) x = minpoly (ZMod g) y
  · exact Or.inl (caseA_of hℓ hlab hx hy hxy hp heq)
  · right
    rcases le_total (minpoly (ZMod g) y).natDegree (minpoly (ZMod g) x).natDegree with h | h
    · exact caseB_of hℓ hlab hx hy hxy hp heq h
    · exact caseB_of hℓ hlab hy hx (Ne.symm hxy) hp.symm (Ne.symm heq) h
end PI.SqfRootsInj.W
