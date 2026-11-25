-- Prove2me | solution 1 for PI.WHw.bC_coeff_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:51.296808+00:00
-- url     : https://prove2.me/submissions/e4d6c174-7ef2-46dd-add6-053be185ec25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ClosedEqNablaC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Theorems.Thm_PI_WHw_bC_euler_monomial
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
theorem _root_.solution {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℂ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) * coeff m f := by
  have hadd : ∀ p q : MvPolynomial (Fin r × Fin n) ℂ,
      rowDiv ℂ a a 1 (p + q) = rowDiv ℂ a a 1 p + rowDiv ℂ a a 1 q := by
    intro p q
    simp [rowDiv, map_add]
  induction f using MvPolynomial.induction_on'
  next m' c =>
    rw [bC_euler_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      simp [smul_eq_mul]
    · simp
  next p q hp hq =>
    rw [hadd, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]
end PI.WHw
