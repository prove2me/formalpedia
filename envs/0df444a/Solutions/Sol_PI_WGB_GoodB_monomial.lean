-- Prove2me | solution 1 for PI.WGB.GoodB_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:39.10206+00:00
-- url     : https://prove2.me/submissions/fb1d0d57-c587-4228-a137-39c48ade8c66

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_GoodB_pow
import Theorems.Thm_PI_WGB_GoodB_prod
import Theorems.Thm_PI_WGB_GoodB_smul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open Formalism.BasicNotions MvPolynomial
variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)
namespace PI.WGB
theorem _root_.solution (hX : ∀ v, GoodB R ψ (X v) (ψ v)) (e : σ →₀ ℕ) (c : ℂ) :
    GoodB R ψ (monomial e c) (Finsupp.weight ψ e) := by
  have he : Finsupp.weight ψ e = ∑ v ∈ e.support, e v * ψ v := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul]
  rw [monomial_eq, ← smul_eq_C_mul, Finsupp.prod, he]
  exact GoodB_smul R ψ c (GoodB_prod R ψ _ _ _ fun v _ => GoodB_pow R ψ (hX v) (e v))
end PI.WGB
