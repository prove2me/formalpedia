-- Prove2me | solution 1 for PI.OpWords.symbolMapMulLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:32.687962+00:00
-- url     : https://prove2.me/submissions/4997d72e-694b-4695-9960-40212ecc9dc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Theorems.Thm_PI_OpWords_Ed_val
import Theorems.Thm_PI_OpWords_kappa_apply
import Theorems.Thm_PI_OpWords_pderiv_inl_xi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution : KappaLeft := by
  intro K _ _ k d a b A
  rw [kappa_apply, kappa_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Module.End.mul_apply, Ed_val, Derivation.map_smul, mul_smul_comm]
  congr 1
  simp only [Derivation.leibniz, pderiv_inl_xi, smul_zero, zero_add, add_zero, smul_eq_mul]
  rw [pderiv_rename Sum.inl_injective, map_mul, rename_X]
  ring
end PI.OpWords
