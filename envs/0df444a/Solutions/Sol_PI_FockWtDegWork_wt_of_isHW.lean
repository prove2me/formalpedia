-- Prove2me | solution 1 for PI.FockWtDegWork.wt_of_isHW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:43.572217+00:00
-- url     : https://prove2.me/submissions/ec2910ad-18f1-4f5d-a10c-4add096470de

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) (h : IsHW act μ v) :
    v ≠ 0 ∧ ∀ a, (act (Eab a a) - ((μ a : ℚ) : ℂ) • (LinearMap.id : Module.End ℂ V)) v = 0 := by
  refine ⟨h.1, fun a => ?_⟩
  have h2 : v ∈ FockH1Action.wtSub act μ := (Submodule.mem_inf.1 h.2).1
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker] at h2
  exact h2 a
end PI.FockWtDegWork
