-- Prove2me | solution 1 for PI.HookSteps.Cap.capelli_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:07:22.500463+00:00
-- url     : https://prove2.me/submissions/d75116df-6141-4dac-aba0-f5ec27bd2de9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
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
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution : CapRel := by
  intro N
  refine ⟨fun a s b t => ?_, fun a s b t => ?_⟩
  · refine LinearMap.ext fun p => ?_
    have e1 : (xo N a s * xo N b t) p = X (a, s) * (X (b, t) * p) := rfl
    have e2 : (xo N b t * xo N a s) p = X (b, t) * (X (a, s) * p) := rfl
    rw [e1, e2]
    exact mul_left_comm _ _ _
  · refine LinearMap.ext fun p => ?_
    have e1 : (dop N b t * xo N a s) p = pderiv (b, t) (X (a, s) * p) := rfl
    have e2 : (xo N a s * dop N b t) p = X (a, s) * pderiv (b, t) p := rfl
    rw [LinearMap.add_apply, e1, e2, Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Pi.single_apply, if_neg (fun e => h (Prod.mk.inj e))]
      simp
end PI.HookSteps.Cap
