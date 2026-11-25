-- Prove2me | solution 1 for PI.WGB.mcF_mulU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:25.704556+00:00
-- url     : https://prove2.me/submissions/f64a7436-7b75-4a19-938c-1d733f624dcb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_rowAct_comp_apply
import Theorems.Thm_PI_WGB_iotaC_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (Y U : Matrix (Fin n) (Fin n) ℂ) (hUU : IsUU U) : mcF f (Y * U) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hU U hUU]
end PI.WGB
