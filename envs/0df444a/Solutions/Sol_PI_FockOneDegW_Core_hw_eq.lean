-- Prove2me | solution 1 for PI.FockOneDegW.Core.hw_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:08.030799+00:00
-- url     : https://prove2.me/submissions/d5a033be-6139-492d-866b-cca32db361c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OneDegOfHalves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Theorems.Thm_PI_FockOneDegW_Core_posC_sb
import Theorems.Thm_PI_FockOneDegW_Core_posC_ne

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
open PI PI.FockOneDegW PI.FockOneDegW.Core
open PI.FockOneDegW PI.FockOneDegW.Inner PI.FockOneDegW.Diag
variable {p q r s : ℕ}
namespace PI.FockOneDegW.Core
theorem _root_.solution (hK : OpsK) (μ : Ix p q → ℚ) (v : Pol p q r s)
    (hv : IsHW (fockAct1 p q r s) μ v) (a b : Ix p q) (h : posC a b) :
    posOp a b v = negOp b a v := by
  have hker : fockAct1 p q r s (Eab a b) v = 0 := by
    have h2 := hv.2
    simp only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at h2
    exact h2.2 a b h
  rw [hK p q r s a b (posC_sb a b h), if_neg (posC_ne a b h), add_zero, LinearMap.sub_apply,
    sub_eq_zero] at hker
  exact hker
end PI.FockOneDegW.Core
