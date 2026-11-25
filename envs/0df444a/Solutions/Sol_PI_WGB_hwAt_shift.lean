-- Prove2me | solution 1 for PI.WGB.hwAt_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:22.6508+00:00
-- url     : https://prove2.me/submissions/9ed3dc53-9823-4528-9694-012aa68714a8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
import Theorems.Thm_PI_WGB_eval_lpMinor_top
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
namespace PI.WGB
theorem _root_.solution {n : ℕ} (κ' : Fin n → ℕ) (d : ℕ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    hwAt (fun i => κ' i + d) Z = Z.det ^ d * hwAt κ' Z := by
  cases n with
  | zero => simp [hwAt, hw, Matrix.det_isEmpty]
  | succ m =>
    unfold hwAt hw
    simp only [map_prod, map_pow]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have hlast : ∀ ν : Fin (m + 1) → ℕ, nuNext ν (Fin.last m) = 0 := by intro ν; simp [nuNext]
    have hmid : ∀ i : Fin m, (κ' i.castSucc + d) - nuNext (fun i => κ' i + d) i.castSucc =
        κ' i.castSucc - nuNext κ' i.castSucc := by
      intro i
      have := i.isLt
      simp only [nuNext, Fin.coe_castSucc]
      split_ifs <;> omega
    simp only [hlast, hmid, Nat.sub_zero]
    rw [eval_lpMinor_top Z _ _ _ (by simp)]
    ring
end PI.WGB
