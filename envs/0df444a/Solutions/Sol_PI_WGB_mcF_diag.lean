-- Prove2me | solution 1 for PI.WGB.mcF_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:41.884173+00:00
-- url     : https://prove2.me/submissions/5e92c166-8a3e-4cf3-be27-c8ed0dd5e66a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_rowAct_comp_apply
import Theorems.Thm_PI_WGB_fockF_smul_left
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
theorem _root_.solution {κ : Fin n → ℕ}
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂˣ) :
    mcF f (Y * Matrix.diagonal fun i => (t i : ℂ)) = (∏ i, (t i : ℂ) ^ κ i) * mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hT t, map_smul, fockF_smul_left]
end PI.WGB
