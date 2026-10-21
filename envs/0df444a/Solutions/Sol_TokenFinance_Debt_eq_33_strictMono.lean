-- Prove2me | solution 1 for TokenFinance.Debt.eq_33_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:40:46.84598+00:00
-- url     : https://prove2.me/submissions/014dc543-15dc-4e76-baa3-75242c9baffb

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

set_option autoImplicit false
open TokenFinance.Debt intervalIntegral

namespace TFDH

lemma cont_pim (c : ℝ) : Continuous (pim c) := by
  unfold pim; fun_prop

lemma cont_debtInv (c D : ℝ) : Continuous (debtInv c D) := by
  unfold debtInv; have := cont_pim c; fun_prop

lemma cont_debtEnt (c D : ℝ) : Continuous (debtEnt c D) := by
  unfold debtEnt; have := cont_pim c; fun_prop

lemma int_sq (c t : ℝ) : ∫ x in c..t, (x - c) ^ 2 / 4 = (t - c) ^ 3 / 12 := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun x => x ^ 2) c]
  simp [integral_pow]
  ring

lemma int_pim_zero (c : ℝ) (hc : 0 ≤ c) : ∫ x in (0:ℝ)..c, pim c x = 0 := by
  have : ∀ x ∈ Set.uIcc (0:ℝ) c, pim c x = 0 := by
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    unfold pim
    have : max (x - c) 0 = 0 := max_eq_right (by linarith [hx.2])
    rw [this]; norm_num
  rw [intervalIntegral.integral_congr this]; simp

lemma int_pim (c θ : ℝ) (hc : 0 ≤ c) (hcθ : c ≤ θ) : ∫ x in (0:ℝ)..θ, pim c x = (θ - c) ^ 3 / 12 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c) ((cont_pim c).intervalIntegrable _ _)
    ((cont_pim c).intervalIntegrable _ _), int_pim_zero c hc, zero_add]
  have : ∀ x ∈ Set.uIcc c θ, pim c x = (x - c) ^ 2 / 4 := by
    intro x hx
    rw [Set.uIcc_of_le hcθ] at hx
    unfold pim
    have : max (x - c) 0 = x - c := max_eq_left (by linarith [hx.1])
    rw [this]
  rw [intervalIntegral.integral_congr this, int_sq]

lemma expect_pim (c θ : ℝ) (hc : 0 ≤ c) (hcθ : c ≤ θ) : expect θ (pim c) = (θ - c) ^ 3 / (12 * θ) := by
  unfold expect
  rw [int_pim c θ hc hcθ]
  by_cases h : θ = 0
  · subst h; simp
  · field_simp

end TFDH

theorem solution (c C0 θ : ℝ) (hc : 0 < c) (hcθ : c < θ) (hC0 : 0 < C0) :
    let F : ℝ → ℝ := fun δ => (θ - c) ^ 3 / (12 * θ) * (-2 * δ ^ 3 + 3 * δ ^ 2) - C0
    F 0 = -C0 ∧ F 1 = npv c C0 θ ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv F δ) ∧
      StrictMonoOn F (Set.Icc 0 1) ∧
      (0 < npv c C0 θ → ∃! δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 ∧ F δ = 0) := by
  intro F
  have hθ : 0 < θ := by linarith
  have hL : 0 < θ - c := by linarith
  have hE : expect θ (pim c) = (θ - c) ^ 3 / (12 * θ) := TFDH.expect_pim c θ hc.le hcθ.le
  have hK : 0 < (θ - c) ^ 3 / (12 * θ) := by positivity
  have hderiv : ∀ δ : ℝ, HasDerivAt F ((θ - c) ^ 3 / (12 * θ) * (-6 * δ ^ 2 + 6 * δ)) δ := by
    intro δ
    have h := ((((hasDerivAt_id δ).pow 3).const_mul (-2)).add (((hasDerivAt_id δ).pow 2).const_mul 3)).const_mul
      ((θ - c) ^ 3 / (12 * θ))
    have h2 := h.sub_const C0
    refine h2.congr_deriv ?_
    simp only [id_eq]
    ring
  have hpos : ∀ δ ∈ Set.Ioo (0 : ℝ) 1, 0 < deriv F δ := by
    intro δ hδ
    rw [(hderiv δ).deriv]
    have : 0 < -6 * δ ^ 2 + 6 * δ := by nlinarith [hδ.1, hδ.2]
    positivity
  have hF0 : F 0 = -C0 := by simp [F]
  have hF1 : F 1 = npv c C0 θ := by
    have : npv c C0 θ = expect θ (pim c) - C0 := rfl
    rw [this, hE]; simp only [F]; ring
  have hmono : StrictMonoOn F (Set.Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    · exact continuous_iff_continuousAt.2 (fun x => (hderiv x).continuousAt) |>.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact hpos x hx
  refine ⟨hF0, hF1, hpos, hmono, ?_⟩
  intro hnpv
  have hcont : ContinuousOn F (Set.Icc 0 1) :=
    (continuous_iff_continuousAt.2 (fun x => (hderiv x).continuousAt)).continuousOn
  have h0 : F 0 < 0 := by rw [hF0]; linarith
  have h1 : 0 < F 1 := by rw [hF1]; exact hnpv
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Ioo (zero_le_one) hcont (show (0:ℝ) ∈ Set.Ioo (F 0) (F 1) from ⟨h0, h1⟩)
  refine ⟨x, ⟨hx, hFx⟩, ?_⟩
  rintro y ⟨hy, hFy⟩
  exact hmono.injOn ⟨hy.1.le, hy.2.le⟩ ⟨hx.1.le, hx.2.le⟩ (by rw [hFy, hFx])
