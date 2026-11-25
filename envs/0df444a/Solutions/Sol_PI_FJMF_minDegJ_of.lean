-- Prove2me | solution 1 for PI.FJMF.minDegJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:21.198732+00:00
-- url     : https://prove2.me/submissions/2e81a48f-b84a-465d-95a5-c3cf9e56decc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_exists_homog_of
import Theorems.Thm_PI_FJMF_hc_mem_hwSub1
import Theorems.Thm_PI_FJMF_hc_mem_hwSub2
import Theorems.Thm_PI_FJMF_span_jset
import Theorems.Thm_PI_FJMF_jset_hc

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
namespace PI.FJMF
theorem _root_.solution (hT1 : PI.FockOneDegW.HwHarmDeg) (hT2 : HwHarmDeg2) : PI.FJM.MinDegJ := by
  intro p q r s μ μ' P hP h0
  simp only [PI.FJM.JH, Submodule.mem_inf] at hP
  obtain ⟨⟨h1, h2⟩, hJ⟩ := hP
  have hJ' := span_jset P hJ
  refine ⟨exists_homog_of P h0 _ fun e he => ?_, exists_homog_of P h0 _ fun e he => ?_⟩
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT1 p q r s μ e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub1 μ P h1 e⟩ j2
  · obtain ⟨j1, j2⟩ := jset_hc P hJ' e
    exact hT2 p q r s μ' e _ (homogeneousComponent_mem e P) ⟨he, hc_mem_hwSub2 μ' P h2 e⟩ j1
end PI.FJMF
