-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.smg2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:15.081076+00:00
-- url     : https://prove2.me/submissions/473ed9b4-7593-4ccf-92da-59cf87afa8e7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_mp_core
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_pert_continuousOn
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_pert_submean
import Theorems.Thm_ReciprocityTheory_AnForm_A_poisson_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} {F : Finset ℂ} (hr : 0 < r) (hF0 : (0 : ℂ) ∉ F)
    (hFr : ∀ f ∈ F, f ∈ ball (0 : ℂ) r)
    (hc : ContinuousOn g (closedBall 0 r \ ↑F))
    (hgrow : ∀ ε > 0, ∀ T : ℝ, ∃ η > 0, ∀ e ∈ F, ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      dist ζ e < η → g ζ + ε * log ‖ζ - e‖ < T)
    (hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑F → g a ≤ circleAverage g a s) :
    g 0 ≤ circleAverage g 0 r := by
  have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 r \ ↑F := fun x hx =>
    ⟨sphere_subset_closedBall hx, fun hxF => by
      have h1 := hFr x hxF
      rw [mem_ball] at h1
      rw [mem_sphere] at hx
      linarith⟩
  obtain ⟨Φ, hΦc, hΦs, hΦ0, hΦm⟩ := poisson_ext hr (hc.mono hsph)
  by_contra hlt
  push Not at hlt
  set γ := g 0 - Φ 0 with hγ
  have hγ0 : 0 < γ := by rw [hγ, hΦ0]; linarith
  obtain ⟨BΦ, hBΦ⟩ : ∃ BΦ, ∀ ζ ∈ closedBall (0 : ℂ) r, -Φ ζ ≤ BΦ := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) r).bddAbove_image hΦc.neg
    exact ⟨M, fun ζ hζ => hM ⟨ζ, hζ, rfl⟩⟩
  set L := (F.card : ℝ) * log (2 * r) - ∑ f ∈ F, log ‖(0 : ℂ) - f‖ with hL
  set ε := γ / (4 * (|L| + 1)) with hε
  set δ := γ / (4 * (r ^ 2 + 1)) with hδ
  have hε0 : 0 < ε := by positivity
  have hδ0 : 0 < δ := by positivity
  have hεL : ε * L < γ / 4 := by
    have : ε * (|L| + 1) = γ / 4 := by rw [hε]; field_simp
    nlinarith [le_abs_self L]
  have hδr : δ * r ^ 2 < γ / 4 := by
    have : δ * (r ^ 2 + 1) = γ / 4 := by rw [hδ]; field_simp
    nlinarith
  set k : ℂ → ℝ := fun ζ => (g ζ - Φ ζ) + pert F 0 ε δ ζ with hk
  have hk0 : k 0 = γ + ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
    simp [hk, pert, hγ]
  have hlog2r : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F, ∀ f ∈ F, log ‖ζ - f‖ ≤ log (2 * r) := by
    intro ζ hζ f hf
    have hne : ζ - f ≠ 0 := sub_ne_zero.2 (fun h => hζ.2 (h ▸ hf))
    apply log_le_log (norm_pos_iff.2 hne)
    have h1 := mem_closedBall_zero_iff.1 hζ.1
    have h2 := mem_ball_zero_iff.1 (hFr f hf)
    calc ‖ζ - f‖ ≤ ‖ζ‖ + ‖f‖ := norm_sub_le _ _
      _ ≤ 2 * r := by linarith
  have hsumle : ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑F,
      ∑ f ∈ F, log ‖ζ - f‖ ≤ (F.card : ℝ) * log (2 * r) := by
    intro ζ hζ
    have := Finset.sum_le_sum (fun f hf => hlog2r ζ hζ f hf)
    simpa using this
  obtain ⟨η, hη, hηp⟩ := hgrow ε hε0
    (k 0 - BΦ - δ * r ^ 2 - ε * ((F.card : ℝ) * |log (2 * r)|))
  apply mp_core (k := k) (c := 0) (ζ0 := 0) (r := r) (E := F) (η := η)
    (by simp [hr.le]) hF0 hη
  ·
    refine ((hc.sub (hΦc.mono Set.sdiff_subset))).add ((pert_continuousOn F 0 ε δ).mono ?_)
    intro x hx; exact hx.2
  ·
    intro ζ hζ
    have hζ' := hsph hζ
    have h1 : g ζ - Φ ζ = 0 := by rw [hΦs ζ hζ]; ring
    have h2 : ‖ζ - 0‖ ^ 2 = r ^ 2 := by
      rw [sub_zero, mem_sphere_zero_iff_norm.1 hζ]
    have h00 : δ * ‖(0 : ℂ) - 0‖ ^ 2 = 0 := by simp
    simp only [hk, pert, h1, h2]
    have := hsumle ζ hζ'
    have h3 := mul_le_mul_of_nonneg_left this hε0.le
    have : ε * L = ε * ((F.card : ℝ) * log (2 * r)) - ε * ∑ f ∈ F, log ‖(0 : ℂ) - f‖ := by
      rw [hL]; ring
    linarith
  ·
    intro e he ζ hζ _ hd
    have hgp := hηp e he ζ hζ hd
    have hsplit : ∑ f ∈ F, log ‖ζ - f‖ = log ‖ζ - e‖ + ∑ f ∈ F.erase e, log ‖ζ - f‖ :=
      (Finset.add_sum_erase F _ he).symm
    have herase : ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ (F.card : ℝ) * |log (2 * r)| := by
      calc ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ∑ f ∈ F.erase e, |log (2 * r)| :=
            Finset.sum_le_sum (fun f hf =>
              (hlog2r ζ hζ f (Finset.mem_of_mem_erase hf)).trans (le_abs_self _))
        _ = ((F.erase e).card : ℝ) * |log (2 * r)| := by simp
        _ ≤ (F.card : ℝ) * |log (2 * r)| := by
            gcongr
            exact Finset.erase_subset e F
    have hq : ‖ζ - 0‖ ^ 2 ≤ r ^ 2 := by
      rw [sub_zero]
      have := mem_closedBall_zero_iff.1 hζ.1
      gcongr
    have hP := hBΦ ζ hζ.1
    have hk' : k ζ = g ζ - Φ ζ + (ε * ∑ f ∈ F, log ‖ζ - f‖ + δ * ‖ζ - 0‖ ^ 2) := rfl
    rw [hk', hsplit]
    have : δ * ‖ζ - 0‖ ^ 2 ≤ δ * r ^ 2 := mul_le_mul_of_nonneg_left hq hδ0.le
    have : ε * ∑ f ∈ F.erase e, log ‖ζ - f‖ ≤ ε * ((F.card : ℝ) * |log (2 * r)|) :=
      mul_le_mul_of_nonneg_left herase hε0.le
    nlinarith
  ·
    intro a s hs hsub'
    have haF : a ∉ F := (hsub' (mem_closedBall_self hs.le)).2
    have hFs : ∀ f ∈ F, f ∉ sphere a s := fun f hf hfs =>
      (hsub' (sphere_subset_closedBall hfs)).2 hf
    obtain ⟨hpi, hpm⟩ := pert_submean (c := 0) (δ := δ) hs hε0.le haF hFs
    have hsB : sphere a |s| ⊆ closedBall (0 : ℂ) r \ ↑F := by
      rw [abs_of_pos hs]
      intro x hx
      have := hsub' (sphere_subset_closedBall hx)
      exact ⟨ball_subset_closedBall this.1, this.2⟩
    have hgi : CircleIntegrable g a s := (hc.mono hsB).circleIntegrable'
    have hΦi : CircleIntegrable Φ a s := (hΦc.mono (hsB.trans Set.sdiff_subset)).circleIntegrable'
    have hav : circleAverage k a s =
        circleAverage g a s - circleAverage Φ a s + circleAverage (pert F 0 ε δ) a s := by
      have e1 := circleAverage_fun_add (hgi.sub hΦi) hpi
      have e2 : circleAverage (g - Φ) a s = circleAverage g a s - circleAverage Φ a s :=
        circleAverage_fun_sub hgi hΦi
      simp only [Pi.sub_apply] at e1
      rw [hk, e1, e2]
    have hΦa : circleAverage Φ a s = Φ a :=
      hΦm a s hs (fun x hx => (hsub' hx).1)
    have hga := hsub a s hs hsub'
    rw [hav, hΦa]
    have : 0 < δ * s ^ 2 := by positivity
    simp only [hk]
    linarith
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
