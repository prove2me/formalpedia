-- Prove2me | solution 1 for PI.WGB.gram_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:05.471174+00:00
-- url     : https://prove2.me/submissions/21762d25-e528-4ef5-aee7-b9a8040161c9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Theorems.Thm_PI_WGB_transpose_conj_comm
import Theorems.Thm_PI_WGB_fockF_rowAct_right
import Theorems.Thm_PI_WGB_iotaC_conj
import Theorems.Thm_PI_WGB_iotaC_mul
import Theorems.Thm_PI_WGB_mc_hw
import Theorems.Thm_PI_WGB_rowAct_comp_apply


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
namespace PI.WGB
theorem _root_.solution {n k : ℕ} {f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ} (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (g g' : Matrix (Fin n) (Fin n) ℂ) :
    fockF (rowAct ℂ (iotaC ℂ n k g).transpose f) (rowAct ℂ (iotaC ℂ n k g').transpose f) =
      fockF f f * hwAt κ (g'.conjTranspose * g) := by
  have e1 : (iotaC ℂ n k g).transpose * (iotaC ℂ n k g').transpose.conjTranspose =
      (iotaC ℂ n k (g'.conjTranspose * g)).transpose := by
    rw [iotaC_mul, iotaC_conj, Matrix.transpose_mul, transpose_conj_comm]
  rw [fockF_rowAct_right, rowAct_comp_apply, e1]
  exact mc_hw κ hκ hU hT _
end PI.WGB
