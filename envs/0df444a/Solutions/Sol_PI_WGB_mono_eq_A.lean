-- Prove2me | solution 1 for PI.WGB.mono_eq_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:54.442734+00:00
-- url     : https://prove2.me/submissions/db0b5b48-c0af-41e3-97b9-1f0341105246

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_CoeffRowActDiagA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_StepACleared
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col
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
theorem _root_.solution (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : m ∈ g.support) (hne : ∏ v, x v ^ m v ≠ 0) : m = mStarA kap ν := by
  have hz : ∀ v, x v = 0 → m v = 0 := by
    intro v hv
    by_contra h
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, zero_pow h]))
  have htop : ∀ (a : Fin n) (s : Fin (n + 1)), s ≠ Fin.castSucc a → m (Fin.castSucc a, s) = 0 :=
    fun a s hs => hz _ (hx _ _ (by simp) (Ne.symm hs))
  have hdiag : ∀ a : Fin n, m (Fin.castSucc a, Fin.castSucc a) = kap a := by
    intro a
    rw [← hrow m hm a, Finset.sum_eq_single (Fin.castSucc a)]
    · intro s _ hs
      exact htop a s hs
    · simp
  have hcolsum : ∀ j, ∑ ρ, m (ρ, j) = ν j := by
    intro j
    rw [← lhwline_weight_col, hcol (mem_support_iff.mp hm)]
  ext ⟨ρ, s⟩
  induction ρ using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last =>
      have h := hcolsum (Fin.last n)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun a _ => htop a _ (Fin.castSucc_lt_last a).ne'),
        zero_add] at h
      rw [mStarA_ll, h]
    | cast k =>
      have h := hcolsum (Fin.castSucc k)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_single k] at h
      · rw [hdiag] at h
        rw [mStarA_lc]
        omega
      · intro b _ hb
        exact htop b _ (fun e => hb (Fin.castSucc_injective _ e).symm)
      · simp
  | cast a =>
    induction s using Fin.lastCases with
    | last =>
      rw [mStarA_cl]
      exact htop a _ (Fin.castSucc_lt_last a).ne'
    | cast k =>
      rw [mStarA_cc]
      split_ifs with hka
      · subst hka
        exact hdiag k
      · exact htop a _ (fun e => hka (Fin.castSucc_injective _ e))
end PI.WGB
