-- Prove2me | solution 1 for PI.WGB.mcF_Lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:42.988548+00:00
-- url     : https://prove2.me/submissions/3f4362ee-5b26-4e38-b3f6-dd955d795919

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Theorems.Thm_PI_WGB_rowAct_comp_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockRowAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_iotaC_conj
import Theorems.Thm_PI_WGB_iotaC_mul
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
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (L Y : Matrix (Fin n) (Fin n) ℂ) (hL : IsUU L.conjTranspose) : mcF f (L * Y) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, fockRowAdj (n + k) (n + k)]
  have : ((iotaC ℂ n k L).transpose).conjTranspose = (iotaC ℂ n k L.conjTranspose).transpose := by
    rw [iotaC_conj]; ext i j; simp
  rw [this, hU _ hL]
end PI.WGB
