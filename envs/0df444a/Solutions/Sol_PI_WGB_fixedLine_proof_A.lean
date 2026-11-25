-- Prove2me | solution 1 for PI.WGB.fixedLine_proof_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:08.810458+00:00
-- url     : https://prove2.me/submissions/68ed8fc7-eacf-486e-aacb-02edce635450

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ProdMkPtA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FixedLineProofA
import Theorems.Thm_PI_WGB_eps_A
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_weight_col
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_WGB_eval_D_A
import Theorems.Thm_PI_WGB_fixed_rowDeg_A
import Theorems.Thm_PI_WGB_mStarA_cc
import Theorems.Thm_PI_WGB_mStarA_cl
import Theorems.Thm_PI_WGB_mStarA_lc
import Theorems.Thm_PI_WGB_mStarA_ll
import Theorems.Thm_PI_WGB_natW_add_A
import Theorems.Thm_PI_WGB_props_A
import Theorems.Thm_PI_WGB_vanishA
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
theorem _root_.solution : FixedLine := by
  intro n N h lam mu f₁ f₂ hf₁ hf₂ hx₁ hx₂ hne
  subst h
  obtain ⟨hcol₁, hR₁, hC₁, hrow₁⟩ := props_A lam mu f₁ hf₁ hx₁
  obtain ⟨hcol₂, hR₂, hC₂, hrow₂⟩ := props_A lam mu f₂ hf₂ hx₂
  have hc₂ : coeff (mStarA (kapA lam mu) lam.natW) f₂ ≠ 0 := by
    intro h0
    apply hne
    exact vanishA f₂ hR₂ hC₂ (fun D hD => by
      rw [eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, h0, zero_mul])
  refine ⟨⟨coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂, ?_⟩, ?_⟩
  · set c := coeff (mStarA (kapA lam mu) lam.natW) f₁ / coeff (mStarA (kapA lam mu) lam.natW) f₂ with hcdef
    have hg : f₁ - c • f₂ = 0 := by
      apply vanishA
      · intro x a b t hab hb
        have e1 := hR₁ x a b t hab hb
        have e2 := hR₂ x a b t hab hb
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro x l j c' hlj
        have e1 := hC₁ x l j c' hlj
        have e2 := hC₂ x l j c' hlj
        simp only at e1 e2
        simp only [map_sub, smul_eval, e1, e2]
      · intro D hD
        rw [map_sub, smul_eval, eval_D_A (kapA lam mu) lam.natW f₁ hcol₁ hrow₁ D hD,
          eval_D_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ D hD, hcdef]
        field_simp
        ring
    exact sub_eq_zero.mp hg
  · have hmS : mStarA (kapA lam mu) lam.natW ∈ f₂.support := mem_support_iff.mpr hc₂
    have hmu : ∀ a : Fin n, ((kapA lam mu a : ℕ) : ℤ) + lam.detShift = mu.w a := by
      intro a
      have hrd := fixed_rowDeg_A lam mu f₂ hx₂ _ hmS a
      have hsum : ∑ s, mStarA (kapA lam mu) lam.natW (Fin.castSucc a, s) = kapA lam mu a := by
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hsum] at hrd
      exact hrd
    have hleA : ∀ a : Fin n, kapA lam mu a ≤ lam.natW (Fin.castSucc a) := by
      intro a
      have hcs : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) = lam.natW (Fin.castSucc a) := by
        rw [← lhwline_weight_col, hcol₂ hc₂]
      have hcs2 : ∑ ρ, mStarA (kapA lam mu) lam.natW (ρ, Fin.castSucc a) =
          kapA lam mu a + (lam.natW (Fin.castSucc a) - kapA lam mu a) := by
        rw [Fin.sum_univ_castSucc]
        simp [Finset.sum_ite_eq']
      omega
    intro i
    have hcast : (⟨i.1, by omega⟩ : Fin (n + 1)) = Fin.castSucc i := Fin.ext rfl
    have hnat := natW_add_A lam (Fin.castSucc i)
    have h1 := hmu i
    have h2 := hleA i
    constructor
    · rw [hcast]
      omega
    · by_cases hi : i.val + 1 < n
      · have hcast' : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.castSucc ⟨i.val + 1, hi⟩ := Fin.ext rfl
        have h3 := eps_A (kapA lam mu) lam.natW f₂ hcol₂ hrow₂ hR₂ hC₂ hc₂ i ⟨i.val + 1, hi⟩ rfl
          (hleA ⟨i.val + 1, hi⟩)
        have hnat' := natW_add_A lam (Fin.castSucc ⟨i.val + 1, hi⟩)
        rw [hcast']
        omega
      · have hlast : (⟨i.1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
        have hds : lam.w (Fin.last n) = lam.detShift := by
          unfold DomWeight.detShift
          rw [dif_pos (by omega)]
          congr 1
        rw [hlast, hds]
        omega
end PI.WGB
