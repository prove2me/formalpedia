-- Prove2me | solution 1 for PI.FJMF.hc_mem_hwSub2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:07.257554+00:00
-- url     : https://prove2.me/submissions/7d6691fb-2c0d-41f6-ae15-919b55f2a2b4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_supp_hc
import Theorems.Thm_PI_FJMF_posC_sb
import Theorems.Thm_PI_FJMF_homogeneous_component_raise_second
import Theorems.Thm_PI_FockOneDegW_Core_posC_sb
import Theorems.Thm_PI_WFJM_mem_hwSub2


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
open PI PI.FJMF
variable {p q r s : ℕ}
namespace PI.FJMF
theorem _root_.solution (μ : Ix r s → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct2 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct2 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub2] at hP ⊢
  refine ⟨fun m hm c => hP.1 m (supp_hc hm) c, fun c d hcd => ?_⟩
  rw [← homogeneous_component_raise_second (posC_sb hcd), hP.2 c d hcd, map_zero]
end PI.FJMF
