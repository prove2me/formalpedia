-- Prove2me | solution 1 for PI.EF.far_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:46.652406+00:00
-- url     : https://prove2.me/submissions/08c2378a-3ba7-4a9e-bae0-7e92ff2fda20

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Theorems.Thm_PI_EF_DZ_facts
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_ctr_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_im
attribute [local simp] PI.EF.ctr_re



set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {Cw : ℝ} (hW : ZerosWindowWith Cw) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {t : ℝ} (s : ℂ) (hs : s.im = t) (E : Finset ℂ)
    (hE : ∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) :
    ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      Cw * Real.log (N * (|t + 2| + 2)) + Cw * Real.log (N * (|t - 2| + 2)) := by
  classical
  have hE' : ∀ ρ ∈ E, 1 ≤ ‖s - ρ‖ ∧ (ρ ∈ ZerosNear χ (t + 2) ∨ ρ ∈ ZerosNear χ (t - 2)) := by
    intro ρ hρ
    obtain ⟨hD, hN, h0⟩ := hE ρ hρ
    obtain ⟨-, hL, him, hcase⟩ := DZ_facts hZL hχ hD
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
      rcases hcase with h | ⟨h, -⟩
      · exact h
      · exact absurd h h0
    have hfar : 1 < |ρ.im - t| := by
      by_contra hc
      push_neg at hc
      exact hN ⟨hstrip.1, hstrip.2, hc, hL⟩
    refine ⟨?_, ?_⟩
    · calc (1 : ℝ) ≤ |ρ.im - t| := hfar.le
        _ = |(s - ρ).im| := by rw [Complex.sub_im, hs, abs_sub_comm]
        _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    · rcases le_or_gt 0 (ρ.im - t) with h | h
      · left
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_nonneg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_neg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
  obtain ⟨hfinP, hsumP⟩ := hW N χ hχ (t + 2)
  obtain ⟨hfinM, hsumM⟩ := hW N χ hχ (t - 2)
  have step1 : ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ E, (mult χ ρ : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [norm_div]
    have h1 := (hE' ρ hρ).1
    have hc : ‖(mult χ ρ : ℂ)‖ = (mult χ ρ : ℝ) := by
      first
        | exact Complex.norm_natCast _
        | simp
    rw [hc]
    exact div_le_self (Nat.cast_nonneg _) h1
  have step2 : ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤
      ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
    have hsub : E ⊆ hfinP.toFinset ∪ hfinM.toFinset := by
      intro ρ hρ
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact (hE' ρ hρ).2
    calc ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ hfinP.toFinset ∪ hfinM.toFinset, (mult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hP : ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t + 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t + 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinP).symm
      _ ≤ _ := hsumP
  have hM : ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t - 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t - 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinM).symm
      _ ≤ _ := hsumM
  linarith
end PI.EF
