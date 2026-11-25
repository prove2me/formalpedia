-- Prove2me | solution 1 for PI.WGB.eval_lpMinor_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:07:21.905855+00:00
-- url     : https://prove2.me/submissions/a05f6eb0-0e75-4fb8-8070-8a59210f8d55

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
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
open Formalism.REAL (fockF)
variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)
variable {f}
namespace PI.WGB
theorem _root_.solution (s : ℕ) (h1 h2 : s ≤ n) :
    eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (lpMinor ℂ s h1 h2) = 1 := by
  rw [lpMinor, RingHom.map_det]
  have : (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)) = 1 := by
    ext p q
    simp [Matrix.one_apply, Fin.castLE_inj]
  rw [this, Matrix.det_one]
end PI.WGB
