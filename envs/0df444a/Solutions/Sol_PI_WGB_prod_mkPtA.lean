-- Prove2me | solution 1 for PI.WGB.prod_mkPtA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:06:12.050261+00:00
-- url     : https://prove2.me/submissions/bd364c05-2e9f-4bfe-a100-b38726d8426d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
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


attribute [local simp] PI.WGB.mStarA_cc
attribute [local simp] PI.WGB.mStarA_cl
attribute [local simp] PI.WGB.mStarA_lc
attribute [local simp] PI.WGB.mStarA_ll

set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) :
    ∏ v, mkPtA dv z v ^ (mStarA kap ν) v =
      (∏ a, dv a ^ kap a) * (∏ k : Fin n, z (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k)) *
        z (Fin.last n) ^ ν (Fin.last n) := by
  have hpw : ∀ a' k : Fin n, (if k = a' then dv a' else 0) ^ (if k = a' then kap a' else 0) =
      if k = a' then dv a' ^ kap a' else 1 := by
    intro a' k
    split_ifs <;> simp
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_castSucc, mkPtA, hpw, mul_assoc]
end PI.WGB
