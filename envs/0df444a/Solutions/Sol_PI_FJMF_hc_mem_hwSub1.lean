-- Prove2me | solution 1 for PI.FJMF.hc_mem_hwSub1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:35.850018+00:00
-- url     : https://prove2.me/submissions/fe980447-328f-4d45-90c6-55165e1abc08

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_supp_hc
import Theorems.Thm_PI_FJMF_posC_sb
import Theorems.Thm_PI_FJMF_homogeneous_component_raise_first
import Theorems.Thm_PI_FockOneDegW_Core_posC_sb
import Theorems.Thm_PI_WFJM_mem_hwSub1


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
theorem _root_.solution (μ : Ix p q → ℚ) (P : Pol p q r s) (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : ℕ) :
    homogeneousComponent e P ∈ hwSub (fockAct1 p q r s) μ := by
  rw [PI.WFJM.mem_hwSub1] at hP ⊢
  refine ⟨fun m hm a => hP.1 m (supp_hc hm) a, fun a b hab => ?_⟩
  rw [← homogeneous_component_raise_first (posC_sb hab), hP.2 a b hab, map_zero]
end PI.FJMF
