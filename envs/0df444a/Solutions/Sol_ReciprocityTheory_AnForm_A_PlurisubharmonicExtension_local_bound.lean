-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.local_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:20.908976+00:00
-- url     : https://prove2.me/submissions/52c2d9f3-681f-4453-acaa-855cea65276e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_line_coord
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_slice_step

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
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (hU : IsOpen U) (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {p : Fin D → ℂ} (hp : p ∈ U) : ∃ ρ > 0, ∃ M, ∀ z ∈ ball p ρ \ coordDiv S, u z ≤ M := by
  classical
  obtain ⟨R, hR0, hRU⟩ := Metric.isOpen_iff.1 hU p hp
  have e0 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have e1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R / 2 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (half_pos hR0))
  have e2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ i ∈ S, p i ≠ 0 → r < ‖p i‖ / 4 := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases h0 : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => absurd h0 h)
    · have h4 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖p i‖ / 4 :=
        nhdsWithin_le_nhds (eventually_lt_nhds (div_pos (norm_pos_iff.2 h0) (by norm_num : (0 : ℝ) < 4)))
      exact h4.mono (fun _ h _ => h)
  obtain ⟨r, hr0, hrR, hrp⟩ := (e0.and (e1.and e2)).exists
  set L : Set (Fin D → ℂ) := closedBall p (3 * r / 2) ∩ ⋂ i ∈ S, {y | r / 2 ≤ ‖y i‖} with hL
  have hLc : IsCompact L := (isCompact_closedBall p _).inter_right
    (isClosed_biInter fun i _ => isClosed_le continuous_const (continuous_apply i).norm)
  have hLsub : L ⊆ U \ coordDiv S := by
    intro y hy
    refine ⟨hRU ?_, ?_⟩
    · have h1 := hy.1
      rw [mem_closedBall] at h1
      rw [mem_ball]
      linarith
    · rintro ⟨i, hi, hyi⟩
      have h1 := Set.mem_iInter₂.1 hy.2 i hi
      simp only [Set.mem_setOf_eq, hyi, norm_zero] at h1
      linarith
  obtain ⟨Mb, hMb⟩ := hLc.bddAbove_image (hc.mono hLsub)
  refine ⟨r / 2, half_pos hr0, Mb, ?_⟩
  have key : ∀ F : Finset (Fin D), (∀ i ∈ F, i ∈ S ∧ p i = 0) → ∀ x : Fin D → ℂ, x ∉ coordDiv S →
      (∀ i, dist (x i) (p i) < 3 * r / 2) → (∀ i ∈ S, p i = 0 → i ∉ F → r / 2 < ‖x i‖) →
      (∀ i ∈ F, ‖x i‖ < r / 2) → ∃ y ∈ L, u x ≤ u y := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _ x _ hxd hxm _
      refine ⟨x, ⟨?_, ?_⟩, le_rfl⟩
      · rw [mem_closedBall, dist_pi_le_iff (by linarith)]
        exact fun i => (hxd i).le
      · refine Set.mem_iInter₂.2 fun i hi => ?_
        show r / 2 ≤ ‖x i‖
        by_cases h0 : p i = 0
        · exact (hxm i hi h0 (by simp)).le
        · have h1 := hrp i hi h0
          have h2 := hxd i
          rw [dist_eq_norm] at h2
          have h3 := norm_sub_norm_le (p i) (x i)
          rw [norm_sub_rev] at h3
          linarith
    | @insert j F hjF ih =>
      intro hF x hxS hxd hxm hxF
      have hj := hF j (Finset.mem_insert_self j F)
      have hxj : ‖x j‖ < r / 2 := hxF j (Finset.mem_insert_self j F)
      have hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • ej j ∈ U := by
        intro ζ hζ
        rw [mem_closedBall, dist_zero_right] at hζ
        apply hRU
        rw [mem_ball, dist_pi_lt_iff hR0]
        intro i
        rw [line_coord, dist_eq_norm]
        split_ifs with hij
        · subst hij
          rw [hj.2, sub_zero]
          exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
        · rw [add_zero, ← dist_eq_norm]
          linarith [hxd i]
      obtain ⟨ζ, hζ, hle⟩ := slice_step hU1 hc hpsh hg hj.1 hr0 hxS (by linarith) hdisc
      rw [mem_sphere, dist_zero_right] at hζ
      have hnew : r / 2 < ‖x j + ζ‖ := by
        have h1 := norm_sub_norm_le ζ (-(x j))
        rw [norm_neg, sub_neg_eq_add, add_comm] at h1
        linarith
      have hS' : x + ζ • ej j ∉ coordDiv S := by
        rintro ⟨i, hi, h0⟩
        rw [line_coord] at h0
        split_ifs at h0 with hij
        · subst hij
          rw [h0, norm_zero] at hnew
          linarith
        · rw [add_zero] at h0
          exact hxS ⟨i, hi, h0⟩
      have hd' : ∀ i, dist ((x + ζ • ej j) i) (p i) < 3 * r / 2 := by
        intro i
        rw [line_coord]
        split_ifs with hij
        · subst hij
          rw [hj.2, dist_zero_right]
          exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)
        · rw [add_zero]
          exact hxd i
      have hm' : ∀ i ∈ S, p i = 0 → i ∉ F → r / 2 < ‖(x + ζ • ej j) i‖ := by
        intro i hi h0 hiF
        rw [line_coord]
        split_ifs with hij
        · subst hij
          exact hnew
        · rw [add_zero]
          exact hxm i hi h0 (by simp [hij, hiF])
      have hF' : ∀ i ∈ F, ‖(x + ζ • ej j) i‖ < r / 2 := by
        intro i hi
        have hij : i ≠ j := fun h => hjF (h ▸ hi)
        rw [line_coord, if_neg hij, add_zero]
        exact hxF i (Finset.mem_insert_of_mem hi)
      obtain ⟨y, hyL, hy⟩ := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)) (x + ζ • ej j)
        hS' hd' hm' hF'
      exact ⟨y, hyL, hle.trans hy⟩
  intro z ⟨hzb, hzS⟩
  rw [mem_ball, dist_pi_lt_iff (half_pos hr0)] at hzb
  have hd : ∀ i, dist (z i) (p i) < 3 * r / 2 := fun i => by linarith [hzb i]
  have hm : ∀ i ∈ S, p i = 0 → i ∉ S.filter (fun i => p i = 0) → r / 2 < ‖z i‖ :=
    fun i hi h0 hiT => absurd (Finset.mem_filter.2 ⟨hi, h0⟩) hiT
  have hF : ∀ i ∈ S.filter (fun i => p i = 0), ‖z i‖ < r / 2 := by
    intro i hi
    have h1 := hzb i
    rw [(Finset.mem_filter.1 hi).2, dist_zero_right] at h1
    exact h1
  obtain ⟨y, hyL, hy⟩ := key (S.filter (fun i => p i = 0)) (fun i hi => Finset.mem_filter.1 hi) z hzS hd hm hF
  exact hy.trans (hMb ⟨y, hyL, rfl⟩)
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
