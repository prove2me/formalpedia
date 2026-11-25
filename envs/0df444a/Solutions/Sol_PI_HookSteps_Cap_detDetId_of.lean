-- Prove2me | solution 1 for PI.HookSteps.Cap.detDetId_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:35.179297+00:00
-- url     : https://prove2.me/submissions/0b7bb60b-2e6e-46ff-98f7-afaabc275cbf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial
namespace PI.HookSteps.Cap
theorem _root_.solution (hA : CapAbsMain) (hS : CapSquare) (hL : CapLeft) (hR : CapRel) :
    DetDetId := by
  intro N
  obtain ⟨h1, h2⟩ := hR N
  have h := hA (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) (Fin N) (Fin N) (xo N) (dop N)
    h1 h2 N id id
  simp only [id_eq, smul_sub, Finset.sum_sub_distrib] at h
  rw [hS N, hL N]
  exact (sub_eq_zero.1 h).symm
end PI.HookSteps.Cap
