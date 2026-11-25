-- Prove2me | solution 1 for PI.FJMF.jset_hc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:30.432893+00:00
-- url     : https://prove2.me/submissions/69cc692b-4d41-4290-90e3-0d32d112a549

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KroneckerOneRightSwap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MinDeg
import Theorems.Thm_PI_FJMF_low_hc
import Theorems.Thm_PI_FJMF_low_sum
import Theorems.Thm_PI_FJM_jointHarmonicsIffLaplacians
import Theorems.Thm_PI_FockOneDegW_Core_key
import Theorems.Thm_PI_WFJM_hc_dd
import Theorems.Thm_PI_WFJM_jointHarmonicsIffLaplacians


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
theorem _root_.solution (P : Pol p q r s) (hP : P ∈ Jset p q r s) (e : ℕ) :
    homogeneousComponent e P ∈ Jset p q r s := by
  have key := PI.FJM.jointHarmonicsIffLaplacians p q r s
  obtain ⟨a1, a2, a3, a4⟩ := (key P).1 hP
  refine (key _).2 ⟨fun i j => ?_, fun i j => ?_, fun k l => ?_, fun k l => ?_⟩
  · exact low_hc _ (by unfold PI.FJM.lapA; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a1 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapB; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a2 i j) e
  · exact low_hc _ (by unfold PI.FJM.lapC; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a3 k l) e
  · exact low_hc _ (by unfold PI.FJM.lapD; exact low_sum _ _ fun _ => PI.WFJM.hc_dd _ _) P (a4 k l) e
end PI.FJMF
