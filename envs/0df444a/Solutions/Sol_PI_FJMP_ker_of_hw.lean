-- Prove2me | solution 1 for PI.FJMP.ker_of_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:35.663285+00:00
-- url     : https://prove2.me/submissions/873563f5-5f9c-42d8-b95f-3a1c6a10f5f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

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
theorem _root_.solution {p q : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub act μ) (a b : Ix p q) (hab : posC a b) : act (Eab a b) v = 0 := by
  unfold hwSub at hv
  have h := (Submodule.mem_inf.mp hv).2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h
  exact h a b hab
end PI.FJMP
