-- Prove2me | solution 1 for PI.WGB.GoodB_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:56.837843+00:00
-- url     : https://prove2.me/submissions/f2bba4c9-e150-4189-a849-2eea4b352e7c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB
import Theorems.Thm_PI_WGB_GoodB_mul
import Theorems.Thm_PI_WGB_GoodB_one
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
theorem _root_.solution {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : ∀ k : ℕ, GoodB R ψ (p ^ k) (k * d)
  | 0 => by simpa using GoodB_one R ψ
  | k + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact GoodB_mul R ψ (solution hp k) hp
end PI.WGB
