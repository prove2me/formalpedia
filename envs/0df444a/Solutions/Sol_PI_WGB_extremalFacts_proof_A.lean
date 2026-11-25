-- Prove2me | solution 1 for PI.WGB.extremalFacts_proof_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:28.589205+00:00
-- url     : https://prove2.me/submissions/ab3b58d5-831a-4c8d-abb1-af7a5d7d11b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Theorems.Thm_PI_WGB_natW_add_A
import Theorems.Thm_PI_WGB_natW_anti_A
import Theorems.Thm_PI_WGB_sqAct_mem_nabla_A
import Theorems.Thm_PI_WGB_rowAct_hw_A
import Theorems.Thm_PI_WGB_det_unitri_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowActDiagWeight
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
namespace PI.WGB
theorem _root_.solution : ExtremalFacts := by
  intro n mu
  refine ⟨?_, ?_, fun g s hs => sqAct_mem_nabla_A n mu g s hs⟩
  · intro g hl hd
    unfold sqAct detPow extremal
    rw [det_unitri_A n g hl hd, one_zpow, Units.val_one, one_smul]
    apply rowAct_hw_A
    · intro i j hij
      simp only [Matrix.transpose_apply]
      exact hl j i hij
    · intro i
      simp only [Matrix.transpose_apply]
      exact hd i
  · intro t
    unfold sqAct detPow extremal
    have hdiag : ((diagGL ℂ n t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).transpose =
        Matrix.diagonal fun a => (t a : ℂ) := by
      simp [diagGL]
    rw [hdiag, Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ n n _ _ _
      (Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl mu.natW (natW_anti_A mu)), smul_smul]
    congr 1
    have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ n t) = ∏ a, t a := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, diagGL, Matrix.det_diagonal]
    have hrow : ∀ a : Fin n, Formalism.GradedWeylDivisibility.rowNu (r := n) mu.natW a = mu.natW a := by
      intro a
      simp [Formalism.GradedWeylDivisibility.rowNu]
    simp only [hrow, hdet]
    have key : (∏ a, t a) ^ mu.detShift * ∏ a, t a ^ ((mu.natW a : ℕ) : ℤ) = ∏ a, t a ^ mu.w a := by
      rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← zpow_add, add_comm, natW_add_A]
    rw [← key, Units.val_mul, Units.coe_prod]
    simp [zpow_natCast]
end PI.WGB
