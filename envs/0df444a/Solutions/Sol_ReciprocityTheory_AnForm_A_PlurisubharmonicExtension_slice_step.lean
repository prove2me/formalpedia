-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.slice_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:34.55152+00:00
-- url     : https://prove2.me/submissions/c5c13bdc-bc91-4ca1-bda5-80434767e8f5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_psh_line
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_line_coord
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_loglog_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_exists_sphere_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_smg2


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
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C : ℝ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (hU1 : U ⊆ ball 0 1) (hc : ContinuousOn u (U \ coordDiv S))
    (hpsh : IsPsh (U \ coordDiv S) u)
    (hg : ∀ z ∈ U \ coordDiv S, u z ≤ C * log (exp 1 + ∑ i ∈ S, log ‖z i‖⁻¹))
    {x : Fin D → ℂ} {j : Fin D} (hj : j ∈ S) {r : ℝ} (hr : 0 < r) (hxA : x ∉ coordDiv S)
    (hxj : ‖x j‖ < r) (hdisc : ∀ ζ ∈ closedBall (0 : ℂ) r, x + ζ • ej j ∈ U) :
    ∃ ζ ∈ sphere (0 : ℂ) r, u x ≤ u (x + ζ • ej j) := by
  have hxi : ∀ i ∈ S, x i ≠ 0 := fun i hi h0 => hxA ⟨i, hi, h0⟩
  have hgood : ∀ ζ ∈ closedBall (0 : ℂ) r, ζ ≠ -x j → x + ζ • ej j ∈ U \ coordDiv S := by
    intro ζ hζ hne
    refine ⟨hdisc ζ hζ, ?_⟩
    rintro ⟨i, hi, h0⟩
    rw [line_coord] at h0
    split_ifs at h0 with hij
    · subst hij
      exact hne (by linear_combination h0)
    · rw [add_zero] at h0
      exact hxi i hi h0
  have hx1 : ∀ i, ‖x i‖ < 1 := by
    have h0 := hU1 (hdisc 0 (Metric.mem_closedBall_self hr.le))
    rw [zero_smul, add_zero, mem_ball, dist_zero_right] at h0
    intro i
    exact lt_of_le_of_lt (norm_le_pi_norm x i) h0
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ℝ, a0 = ∑ i ∈ S.erase j, log ‖x i‖⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a0 := by
    rw [ha0def]
    refine Finset.sum_nonneg (fun i _ => ?_)
    rw [Real.log_inv]
    exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) (hx1 i).le)
  have hcont : ContinuousOn (fun ζ : ℂ => u (x + ζ • ej j)) (closedBall 0 r \ ↑({-x j} : Finset ℂ)) := by
    have hmaps : Set.MapsTo (fun ζ : ℂ => x + ζ • ej j) (closedBall 0 r \ ↑({-x j} : Finset ℂ))
        (U \ coordDiv S) := by
      intro ζ hζ
      exact hgood ζ hζ.1 (fun h => hζ.2 (by simp [h]))
    have hcf : Continuous (fun ζ : ℂ => x + ζ • ej j) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ContinuousOn.comp (g := u) (f := fun ζ : ℂ => x + ζ • ej j) hc hcf.continuousOn hmaps
  have hgrow : ∀ ε > 0, ∀ T : ℝ, ∃ η > 0, ∀ e ∈ ({-x j} : Finset ℂ),
      ∀ ζ ∈ closedBall (0 : ℂ) r \ ↑({-x j} : Finset ℂ),
      dist ζ e < η → u (x + ζ • ej j) + ε * log ‖ζ - e‖ < T := by
    intro ε hε T
    obtain ⟨Y, hY⟩ := loglog_bound C a0 ε T hε ha0
    refine ⟨exp (-(max Y 0 + 1)), exp_pos _, ?_⟩
    intro e he ζ hζ hdist
    rw [Finset.mem_singleton] at he
    subst he
    have hne : ζ ≠ -x j := fun h => hζ.2 (by simp [h])
    have hpos : 0 < ‖ζ - -x j‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [dist_eq_norm] at hdist
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = log ‖ζ - -x j‖⁻¹ := ⟨_, rfl⟩
    have hylog : log ‖ζ - -x j‖ = -y := by rw [hy, Real.log_inv, neg_neg]
    have hyY : max Y 0 + 1 ≤ y := by
      have h1 := Real.log_lt_log hpos hdist
      rw [Real.log_exp] at h1
      linarith
    have hsum : ∑ i ∈ S, log ‖(x + ζ • ej j) i‖⁻¹ = y + a0 := by
      rw [← Finset.add_sum_erase S _ hj]
      congr 1
      · rw [line_coord, if_pos rfl, hy, sub_neg_eq_add, add_comm]
      · rw [ha0def]
        apply Finset.sum_congr rfl
        intro i hi
        rw [line_coord, if_neg (Finset.ne_of_mem_erase hi), add_zero]
    have hgz := hg _ (hgood ζ hζ.1 hne)
    rw [hsum] at hgz
    have h1 := hY y (by linarith [le_max_left Y 0]) (by linarith [le_max_right Y 0])
    have h2 : exp 1 + (y + a0) = exp 1 + a0 + y := by ring
    rw [h2] at hgz
    rw [hylog]
    linarith
  have hsub : ∀ a s, 0 < s → closedBall a s ⊆ ball (0 : ℂ) r \ ↑({-x j} : Finset ℂ) →
      u (x + a • ej j) ≤ circleAverage (fun ζ => u (x + ζ • ej j)) a s := by
    intro a s hs hs2
    refine (psh_line hpsh x (ej j) hs (fun ζ hζ => ?_)).2
    have h1 := hs2 hζ
    exact hgood ζ (ball_subset_closedBall h1.1) (fun h => h1.2 (by simp [h]))
  have hF0 : (0 : ℂ) ∉ ({-x j} : Finset ℂ) := by
    rw [Finset.mem_singleton]
    intro h
    exact hxi j hj (by linear_combination h)
  have hFr : ∀ f ∈ ({-x j} : Finset ℂ), f ∈ ball (0 : ℂ) r := by
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    rw [mem_ball, dist_zero_right, norm_neg]
    exact hxj
  have hmean := smg2 hr hF0 hFr hcont hgrow hsub
  have hcs : ContinuousOn (fun ζ : ℂ => u (x + ζ • ej j)) (sphere 0 r) := by
    refine hcont.mono (fun ζ hζ => ⟨sphere_subset_closedBall hζ, fun h => ?_⟩)
    have h1 : ζ = -x j := by simpa using h
    rw [mem_sphere, dist_zero_right, h1, norm_neg] at hζ
    linarith
  obtain ⟨ζ, hζ, hle⟩ := exists_sphere_ge hr hcs hmean
  exact ⟨ζ, hζ, by simpa only [zero_smul, add_zero] using hle⟩
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
