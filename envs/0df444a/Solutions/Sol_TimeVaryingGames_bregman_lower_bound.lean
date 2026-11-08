-- Prove2me | solution 1 for TimeVaryingGames.bregman_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:37:10.496239+00:00
-- url     : https://prove2.me/submissions/5ba51e6d-7000-480c-9c43-358ef5bbffa9

import Mathlib
import Definitions.Def_TimeVaryingGames_DGF

open Filter Topology

namespace Aux_TVG_blb

theorem limit_arg (A B : ℝ) (hA : 0 ≤ A) (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * A ≤ B) :
    A ≤ B := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = A - B := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = min (1 / 2) (δ / (2 * (A + 1))) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [ht]; exact lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := by rw [ht]; exact min_le_left _ _
  have ht2 : t ≤ δ / (2 * (A + 1)) := by rw [ht]; exact min_le_right _ _
  have h3 : δ / (2 * (A + 1)) * A ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : t * A ≤ δ / 2 := le_trans (mul_le_mul_of_nonneg_right ht2 hA) h3
  have := h t ht0 (by linarith)
  nlinarith

end Aux_TVG_blb

open TimeVaryingGames in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} {Kc : ℝ} {h : E → ℝ} {gradh : E → E →L[ℝ] ℝ}
    (hdgf : IsDGF C Kc h gradh) {p : E} (hp : p ∈ C) :
    (∀ x ∈ proxDomain C h, Kc / 2 * ‖x - p‖ ^ 2 ≤ bregman h gradh p x) ∧
      ∀ xt : ℕ → E, (∀ t, xt t ∈ proxDomain C h) →
        Tendsto (fun t => bregman h gradh p (xt t)) atTop (𝓝 0) → Tendsto xt atTop (𝓝 p) := by
  have hK := hdgf.modulus_pos
  have part1 : ∀ x ∈ proxDomain C h, Kc / 2 * ‖x - p‖ ^ 2 ≤ bregman h gradh p x := by
    intro x hx
    have hsub := hdgf.gradh_mem x hx
    have hxC : x ∈ C := hx.1
    apply Aux_TVG_blb.limit_arg _ _ (by positivity)
    intro t ht0 ht1
    have hsc := hdgf.strongConvexOn.2 hxC hp (show (0 : ℝ) ≤ 1 - t by linarith) ht0.le
      (show 1 - t + t = (1 : ℝ) by ring)
    have hmem : (1 - t) • x + t • p ∈ C :=
      hdgf.strongConvexOn.1 hxC hp (by linarith) ht0.le (by ring)
    have hg := hsub _ hmem
    have hdiff : (1 - t) • x + t • p - x = t • (p - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hdiff, map_smul, smul_eq_mul] at hg
    simp only [smul_eq_mul] at hsc
    unfold bregman
    have key : t * ((1 - t) * (Kc / 2 * ‖x - p‖ ^ 2)) ≤
        t * (h p - h x - gradh x (p - x)) := by nlinarith
    exact le_of_mul_le_mul_left key ht0
  refine ⟨part1, fun xt hxt hlim => ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun t => Real.sqrt (2 / Kc * bregman h gradh p (xt t))) atTop (𝓝 0) := by
    have := (hlim.const_mul (2 / Kc)).sqrt
    simpa using this
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) hg
  have h1 := part1 (xt t) (hxt t)
  rw [← abs_norm]
  apply Real.abs_le_sqrt
  have e : ‖xt t - p‖ ^ 2 = 2 / Kc * (Kc / 2 * ‖xt t - p‖ ^ 2) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
