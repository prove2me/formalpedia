-- Prove2me | solution 1 for PI.FockOneDegW.HwC.coeff_Ecc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:57.629815+00:00
-- url     : https://prove2.me/submissions/5b170ee5-a19c-47fa-be08-233a543767c0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_CoeffXMulPderivSelf
import Theorems.Thm_PI_FockOneDegW_HwC_coeff_X_mul_pderiv_self
import Theorems.Thm_PI_FockOneDegW_fockAct1_Eab_apply


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
theorem _root_.solution {p q r s : ℕ} (c : Ix p q) (P : Pol p q r s) (β : Ln p q r s →₀ ℕ) :
    coeff β (fockAct1 p q r s (Eab c c) P) = ((wtv β c : ℚ) : ℂ) * coeff β P := by
  classical
  have hline : ∀ l : Ln p q r s, coeff β (omE l l P) =
      (((sgnL l * β l + sgnL l / 2 : ℚ)) : ℂ) * coeff β P := by
    intro l
    by_cases hl : linePos l = true
    · simp only [omE, raiB, lowB, hl, if_true, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, LinearMap.smul_apply,
        Module.End.one_apply, coeff_add, coeff_smul, smul_eq_mul, coeff_X_mul_pderiv_self, sgnL]
      push_cast
      ring
    · have hl' : linePos l = false := by simpa using hl
      have e : coeff β (pderiv l (X l * P)) = ((β l : ℂ) + 1) * coeff β P := by
        rw [coeff_pderiv, add_comm β, coeff_X_mul, mul_comm]
      simp only [omE, raiB, lowB, hl', Bool.false_eq_true, if_false, if_true, LinearMap.add_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe,
        LinearMap.smul_apply, Module.End.one_apply, coeff_add, coeff_neg, coeff_smul, smul_eq_mul, e, sgnL]
      push_cast
      ring
  rw [fockAct1_Eab_apply, coeff_sum]
  simp_rw [hline]
  rw [← Finset.sum_mul]
  congr 1
  unfold wtv
  push_cast
  rw [Finset.sum_add_distrib]
  congr 1
  cases c with
  | inl i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring
  | inr i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring
end PI.FockOneDegW.HwC
