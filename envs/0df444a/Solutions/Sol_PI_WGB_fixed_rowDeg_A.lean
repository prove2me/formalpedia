-- Prove2me | solution 1 for PI.WGB.fixed_rowDeg_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:24.241137+00:00
-- url     : https://prove2.me/submissions/a0d51ecf-d49c-4355-ac53-e462d61b3abf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_PI_WGB_emb_cc_A
import Theorems.Thm_PI_WGB_emb_cl_A
import Theorems.Thm_PI_WGB_emb_lc_A
import Theorems.Thm_PI_WGB_emb_ll_A
import Theorems.Thm_PI_WGB_coeff_rowAct_diag_A
import Theorems.Thm_PI_WGB_zpow_two_inj_A
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
theorem _root_.solution (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : m ∈ f.support) (a : Fin n) :
    ((∑ s, m (Fin.castSucc a, s) : ℕ) : ℤ) + lam.detShift = mu.w a := by
  set t : Fin n → ℂˣ := fun j => if j = a then Units.mk0 2 two_ne_zero else 1 with ht
  have hg := hf.2 t
  have hdiag : ((embGL ℂ n (n + 1) rfl (diagGL ℂ n t) : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).transpose =
      Matrix.diagonal (fun c => if c = Fin.castSucc a then (2 : ℂ) else 1) := by
    ext ρ c
    rw [Matrix.transpose_apply, Matrix.diagonal_apply]
    induction ρ using Fin.lastCases with
    | last =>
      induction c using Fin.lastCases with
      | last => simp [emb_ll_A, (Fin.castSucc_lt_last a).ne']
      | cast c => simp [emb_cl_A, (Fin.castSucc_lt_last c).ne']
    | cast ρ =>
      induction c using Fin.lastCases with
      | last => simp [emb_lc_A, (Fin.castSucc_lt_last ρ).ne]
      | cast c =>
        rw [emb_cc_A]
        simp only [diagGL, Matrix.diagonal_apply, ht, Fin.castSucc_inj]
        by_cases hc : c = ρ
        · subst hc
          by_cases hca : c = a <;> simp [hca]
        · simp [hc, Ne.symm hc]
  have hdet : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) : ℂˣ) : ℂ) = 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hdiag, Matrix.det_diagonal,
      Fintype.prod_ite_eq']
  unfold sqAct detPow at hg
  rw [hdiag] at hg
  have hc := congrArg (coeff m) hg
  rw [coeff_smul, coeff_smul, coeff_rowAct_diag_A, smul_eq_mul, smul_eq_mul, Units.val_zpow_eq_zpow_val, hdet]
    at hc
  have hcf : coeff m f ≠ 0 := mem_support_iff.mp hm
  have hprod : (∏ ρ : Fin (n + 1), (if ρ = Fin.castSucc a then (2 : ℂ) else 1) ^ (∑ j, m (ρ, j))) =
      2 ^ (∑ j, m (Fin.castSucc a, j)) := by
    rw [Finset.prod_eq_single (Fin.castSucc a)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have hmu : ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) = 2 ^ mu.w a := by
    rw [Units.coe_prod, Finset.prod_eq_single a]
    · simp [ht]
    · intro b _ hb
      simp [ht, hb]
    · simp
  rw [hprod, hmu, ← mul_assoc] at hc
  have hc2 := mul_right_cancel₀ hcf hc
  rw [← zpow_natCast, ← zpow_add₀ two_ne_zero] at hc2
  have := zpow_two_inj_A _ _ hc2
  omega
end PI.WGB
