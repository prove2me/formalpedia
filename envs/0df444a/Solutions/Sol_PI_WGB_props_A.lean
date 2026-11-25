-- Prove2me | solution 1 for PI.WGB.props_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:51.513068+00:00
-- url     : https://prove2.me/submissions/cf049d78-9ac6-4ee3-bd14-f24575dfb303

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylPoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_CInv_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_lsat_mem_dualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_fixed_rowDeg_A
import Theorems.Thm_PI_WGB_fixed_rowOp_A
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
theorem _root_.solution (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : f ∈ nablaSq ℂ (n + 1) lam) (hfix : IsFixedW rfl lam mu f) :
    IsWeightedHomogeneous (colW (n + 1) (n + 1)) f lam.natW ∧ RInvA (fun x => eval x f) ∧
      lhwline_CInv (fun x => eval x f) ∧
      ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kapA lam mu a := by
  refine ⟨(lsat_mem_dualWeyl.mp hf).1, ?_, ?_, ?_⟩
  · intro x a b t hab hb
    have ha : a.val < n := lt_trans hab hb
    have h1 : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
    have h2 : b = Fin.castSucc ⟨b.val, hb⟩ := Fin.ext rfl
    simp only
    rw [h1, h2]
    exact fixed_rowOp_A lam mu f hfix _ _ (by rw [Fin.lt_def] at hab ⊢; exact hab) t x
  · exact lhwline_CInv_of f (fun l j hlj c => ((dualWeylPoint ℂ (n + 1) (n + 1) lam.natW f).mp hf).2 l j hlj c)
  · intro m hm a
    have := fixed_rowDeg_A lam mu f hfix m hm a
    unfold kapA
    omega
end PI.WGB
