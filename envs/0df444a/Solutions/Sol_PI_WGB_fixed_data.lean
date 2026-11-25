-- Prove2me | solution 1 for PI.WGB.fixed_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:22.485181+00:00
-- url     : https://prove2.me/submissions/16afe84a-b113-4879-9dbc-7c35b5f6412b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_AevalScaleMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_TransposeConjComm
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
theorem _root_.solution {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ) (c : ℤ) (w : Fin n → ℤ)
    (κ : Fin n → ℕ) (hwκ : ∀ i, (κ i : ℤ) + c = w i)
    (hU0 : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) →
      (∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) →
      ((g : Matrix (Fin n) (Fin n) ℂ).det ^ c) • rowAct ℂ (iotaC ℂ n k g).transpose f = f)
    (hT0 : ∀ t : Fin n → ℂˣ, ((∏ i, (t i : ℂ)) ^ c) •
      rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f = (∏ i, (t i : ℂ) ^ w i) • f) :
    (∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f) ∧
    (∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f) := by
  refine ⟨fun u hu => ?_, fun t => ?_⟩
  · have hdet : u.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular (fun i j h => hu.1 i j h)]
      simp [hu.2]
    have := hU0 (Matrix.GeneralLinearGroup.mkOfDetNeZero u (by rw [hdet]; exact one_ne_zero))
      (fun i j h => hu.1 i j h) (fun i => hu.2 i)
    simpa [hdet] using this
  · have h0 := hT0 t
    have hne : (∏ i, (t i : ℂ)) ^ c ≠ 0 := zpow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i _ => (t i).ne_zero)
    have hw : (∏ i, (t i : ℂ) ^ w i) = (∏ i, (t i : ℂ) ^ κ i) * (∏ i, (t i : ℂ)) ^ c := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hwκ i, zpow_add₀ (t i).ne_zero, zpow_natCast]
    rw [hw, mul_comm, ← smul_smul] at h0
    exact smul_right_injective _ hne h0
end PI.WGB
