-- Prove2me | solution 1 for PI.WHw.bC_euler_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:53.01931+00:00
-- url     : https://prove2.me/submissions/c399287a-d58e-4213-a048-d1a290ada965

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Theorems.Thm_PI_WHw_bC_rowGen_monomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open PI PI.WHw
namespace PI.WHw
theorem _root_.solution {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowDiv ℂ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) • monomial m c := by
  unfold rowDiv
  rw [bC_rowGen_monomial, Polynomial.coeff_C_mul, add_comm (1 : Polynomial _) Polynomial.X,
    Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]
  first
    | rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]
    | simp [nsmul_eq_mul, mul_comm]
    | (rw [MvPolynomial.smul_eq_C_mul, mul_comm]; simp)
end PI.WHw
