-- Prove2me | solution 1 for PI.FJMP.mem_leftHighestWeight_of_isMinimalJointVector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:22.839823+00:00
-- url     : https://prove2.me/submissions/191b383d-8e48-41d5-9c7d-194cd2788541

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
theorem _root_.solution {p q r s : ℕ} {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hM : MinHyp p q r s μ μ' P) : P ∈ hwSub (fockAct1 p q r s) μ := by
  have hM' := hM
  unfold MinHyp at hM'
  have h := hM'.1
  unfold JH at h
  exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp h).1).1
end PI.FJMP
