-- Prove2me | solution 1 for PI.FockOneDegW.HwC.Ecc_of_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:21.505074+00:00
-- url     : https://prove2.me/submissions/c51cc0fc-5add-4d1c-82c4-fc575d2090ac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Theorems.Thm_PI_FockOneDegW_HwC_coeff_Ecc

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
open PI PI.FockOneDegW PI.FockOneDegW.HwC
namespace PI.FockOneDegW.HwC
theorem _root_.solution {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P) (c : Ix p q) :
    fockAct1 p q r s (Eab c c) P = ((ν c : ℚ) : ℂ) • P := by
  ext β
  rw [coeff_Ecc, coeff_smul, smul_eq_mul]
  by_cases hβ : β ∈ P.support
  · rw [hP β hβ c]
  · have h0 : coeff β P = 0 := by simpa [mem_support_iff] using hβ
    rw [h0, mul_zero, mul_zero]
end PI.FockOneDegW.HwC
