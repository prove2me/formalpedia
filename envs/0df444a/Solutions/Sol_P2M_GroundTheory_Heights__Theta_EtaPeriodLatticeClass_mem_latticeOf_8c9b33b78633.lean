-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:52.828641+00:00
-- url     : https://prove2.me/submissions/8399c76b-9971-499e-99ed-300a62ac43e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
open GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
theorem _root_.solution {τ z : ℂ} : z ∈ latticeOf τ ↔ ∃ m n : ℤ, z = m + n * τ := by
  unfold latticeOf
  rw [SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp [zsmul_eq_mul]⟩
end GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
