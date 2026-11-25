-- Prove2me | solution 1 for PI.WGB.coeff_rowAct_diag_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:25.255868+00:00
-- url     : https://prove2.me/submissions/bb92fa52-85f9-402c-8f9f-5e0cb807a338

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_PI_WGB_weight_row_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActDiagWeight
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
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution {r c : ℕ} (s : Fin r → ℂ) (f : MvPolynomial (Fin r × Fin c) ℂ)
    (m : Fin r × Fin c →₀ ℕ) :
    coeff m (rowAct ℂ (Matrix.diagonal s) f) = (∏ ρ, s ρ ^ (∑ j : Fin c, m (ρ, j))) * coeff m f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m' k =>
    rw [rowActDiagWeight ℂ r c s _ _ (isWeightedHomogeneous_monomial _ _ _ rfl), coeff_smul, coeff_monomial,
      smul_eq_mul]
    split_ifs with h
    · subst h
      simp only [weight_row_A]
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end PI.WGB
