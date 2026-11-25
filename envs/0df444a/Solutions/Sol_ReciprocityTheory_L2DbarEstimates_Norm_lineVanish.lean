-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Norm.lineVanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:18:28.931883+00:00
-- url     : https://prove2.me/submissions/65cfda04-818b-4090-bd58-ce249c3dc096

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_HoloSectionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SymmetricSections_RemovableFinset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Norm_removable_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Norm
open Filter Topology Asymptotics
universe u
namespace ReciprocityTheory.L2DbarEstimates.Norm
theorem _root_.solution : lineVanishStatement := by
  intro g B A K N hB hKN hd hgr h0 t ht
  classical
  obtain ⟨c0, hc0⟩ := h0.bound
  have hg0 : g 0 = 0 := by
    have h1 := hc0.self_of_nhds
    rw [zero_pow (by omega : N ≠ 0), norm_zero, mul_zero] at h1
    exact norm_le_zero_iff.mp h1
  by_cases ht0 : t = 0
  · rw [ht0]; exact hg0
  set S : Finset ℂ := insert 0 hB.toFinset with hS
  have hBc : IsOpen Bᶜ := hB.isClosed.isOpen_compl
  have hmemS : ∀ x, x ∉ S ↔ x ≠ 0 ∧ x ∉ B := by intro x; simp [hS]
  set h : ℂ → ℂ := fun x => g x / x ^ N with hh
  have hdh : DifferentiableOn ℂ h (↑S)ᶜ := by
    intro x hx
    have hx' := (hmemS x).mp hx
    have hgx : DifferentiableAt ℂ g x := hd.differentiableAt (hBc.mem_nhds hx'.2)
    exact (hgx.div (differentiableAt_pow N) (pow_ne_zero N hx'.1)).differentiableWithinAt
  have hbd : ∀ c ∈ S, ∃ M : ℝ, ∀ᶠ x in 𝓝[≠] c, ‖h x‖ ≤ M := by
    intro c hc
    by_cases hc0' : c = 0
    · subst hc0'
      refine ⟨c0, ?_⟩
      filter_upwards [nhdsWithin_le_nhds hc0, self_mem_nhdsWithin] with x hx hx0
      have hxn : 0 < ‖x‖ ^ N := pow_pos (norm_pos_iff.mpr hx0) N
      rw [hh]
      simp only [norm_div, norm_pow] at hx ⊢
      rw [div_le_iff₀ hxn]
      exact hx
    · have hcont : ContinuousAt (fun x : ℂ => |A| * (1 + ‖x‖) ^ K / ‖x‖ ^ N) c := by
        apply ContinuousAt.div (by fun_prop) (by fun_prop)
        exact pow_ne_zero N (norm_ne_zero_iff.mpr hc0')
      refine ⟨|A| * (1 + ‖c‖) ^ K / ‖c‖ ^ N + 1, ?_⟩
      have h1 : ∀ᶠ x in 𝓝 c, |A| * (1 + ‖x‖) ^ K / ‖x‖ ^ N < |A| * (1 + ‖c‖) ^ K / ‖c‖ ^ N + 1 :=
        hcont.eventually (gt_mem_nhds (lt_add_one _))
      have h2 : ∀ᶠ x in 𝓝 c, x ≠ 0 := isOpen_compl_singleton.mem_nhds hc0'
      have h3 : ∀ᶠ x in 𝓝[≠] c, x ∉ B := by
        have h4 : ∀ᶠ x in 𝓝 c, x ∉ B \ {c} :=
          (hB.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
        filter_upwards [nhdsWithin_le_nhds h4, self_mem_nhdsWithin] with x hx hxc
        intro hxB
        exact hx ⟨hxB, hxc⟩
      filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, h3] with x hx1 hx2 hx3
      have hxn : 0 < ‖x‖ ^ N := pow_pos (norm_pos_iff.mpr hx2) N
      rw [hh]
      simp only [norm_div, norm_pow]
      refine le_trans ?_ hx1.le
      rw [div_le_div_iff_of_pos_right hxn]
      exact (hgr x hx3).trans (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity))
  obtain ⟨F, hF, hFh⟩ := removable_finset S h hdh hbd
  set R : ℝ := 1 + ∑ b ∈ S, ‖b‖ with hR
  have hR1 : 1 ≤ R := by
    have := Finset.sum_nonneg (fun b (_ : b ∈ S) => norm_nonneg b)
    linarith
  have hfar : ∀ x : ℂ, R ≤ ‖x‖ → x ∉ S := by
    intro x hx hxS
    have := Finset.single_le_sum (fun b (_ : b ∈ S) => norm_nonneg b) hxS
    linarith
  have hlim : Tendsto F (cocompact ℂ) (𝓝 0) := by
    have hev : ∀ᶠ x in cocompact ℂ, R ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)
    have hlim0 : Tendsto (fun x : ℂ => |A| * 2 ^ K / ‖x‖) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [hev] with x hx
    have hxS := hfar x hx
    have hx1 : 1 ≤ ‖x‖ := hR1.trans hx
    have hx' := (hmemS x).mp hxS
    have hxpos : 0 < ‖x‖ := by linarith
    rw [hFh x hxS, hh]
    simp only [norm_div, norm_pow]
    rw [div_le_div_iff₀ (pow_pos hxpos N) hxpos]
    have hg1 : ‖g x‖ ≤ |A| * (2 * ‖x‖) ^ K := by
      refine (hgr x hx'.2).trans ?_
      calc A * (1 + ‖x‖) ^ K ≤ |A| * (1 + ‖x‖) ^ K :=
            mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
        _ ≤ |A| * (2 * ‖x‖) ^ K :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) K)
              (abs_nonneg A)
    have hpow : ‖x‖ ^ K * ‖x‖ ≤ ‖x‖ ^ N := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hx1 hKN
    calc ‖g x‖ * ‖x‖ ≤ |A| * (2 * ‖x‖) ^ K * ‖x‖ := mul_le_mul_of_nonneg_right hg1 hxpos.le
      _ = |A| * 2 ^ K * (‖x‖ ^ K * ‖x‖) := by rw [mul_pow]; ring
      _ ≤ |A| * 2 ^ K * ‖x‖ ^ N := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hF0 : ∀ x, F x = 0 := fun x => hF.apply_eq_of_tendsto_cocompact x hlim
  have htS : t ∉ S := (hmemS t).mpr ⟨ht0, ht⟩
  have h2 : g t / t ^ N = 0 := by
    show h t = 0
    rw [← hFh t htS, hF0 t]
  exact (div_eq_zero_iff.mp h2).resolve_right (pow_ne_zero N ht0)
end ReciprocityTheory.L2DbarEstimates.Norm
