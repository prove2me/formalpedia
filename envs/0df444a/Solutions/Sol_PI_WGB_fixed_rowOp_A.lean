-- Prove2me | solution 1 for PI.WGB.fixed_rowOp_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:39.651728+00:00
-- url     : https://prove2.me/submissions/4f2f3b1c-c44b-4d36-8a5a-fb16b7118c24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFactsProofA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetEmbUnitriA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Theorems.Thm_PI_WGB_emb_cc_A
import Theorems.Thm_PI_WGB_emb_cl_A
import Theorems.Thm_PI_WGB_emb_lc_A
import Theorems.Thm_PI_WGB_emb_ll_A
import Theorems.Thm_PI_WGB_det_emb_unitri_A
import Theorems.Thm_PI_WGB_eval_rowAct_A
import Theorems.Thm_PI_WGB_elemGL_apply_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_Reformulated_B_Qe13_det_emb_unitri_A
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
variable {n : ℕ}
namespace PI.WGB
theorem _root_.solution (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : IsFixedW rfl lam mu f) (a b : Fin n) (hab : a < b) (t : ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) :
    eval (lhwline_rowOp (Fin.castSucc a) (Fin.castSucc b) t x) f = eval x f := by
  have hl : ∀ i j, j < i → ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0 := by
    intro i j hji
    rw [elemGL_apply_A, if_neg (ne_of_gt hji), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hji
  have hd : ∀ i, ((elemGL_A a b hab.ne t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
    intro i
    rw [elemGL_apply_A, if_pos rfl, if_neg]
    · simp
    · rintro ⟨rfl, h⟩
      exact hab.ne h.symm
  have hg := hf.1 (elemGL_A a b hab.ne t) hl hd
  unfold sqAct detPow at hg
  rw [det_emb_unitri_A _ hl hd, one_zpow, Units.val_one, one_smul] at hg
  have h2 := congrArg (eval x) hg
  rw [eval_rowAct_A] at h2
  rw [← h2]
  congr 2
  funext v
  obtain ⟨ρ, s⟩ := v
  simp only [Matrix.transpose_apply, Fin.sum_univ_castSucc, lhwline_rowOp]
  induction ρ using Fin.lastCases with
  | last =>
    simp only [emb_cl_A, emb_ll_A, zero_mul, Finset.sum_const_zero, one_mul, zero_add]
    rw [if_neg (Fin.castSucc_lt_last b).ne']
  | cast ρ =>
    simp only [emb_cc_A, emb_lc_A, zero_mul, add_zero, elemGL_apply_A, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ ρ, if_pos (Finset.mem_univ _)]
    by_cases hρ : ρ = b
    · subst hρ
      rw [if_pos rfl]
      rw [Finset.sum_eq_single a]
      · simp
      · intro c _ hc
        rw [if_neg (fun h => hc h.1.symm)]
      · simp
    · rw [if_neg (fun h => hρ (Fin.castSucc_injective _ h))]
      rw [Finset.sum_eq_zero]
      · simp
      · intro c _
        rw [if_neg (fun h => hρ h.2.symm)]
end PI.WGB
