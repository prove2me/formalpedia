-- Prove2me | solution 1 for ZeroOneIALM.stronglyConvex_isCoercive
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T01:31:13.063809+00:00
-- url     : https://prove2.me/submissions/ac032294-1634-43f7-a36c-4bf5b5a194ad

import Mathlib
import Definitions.Def_ZeroOneIALM_Assumptions

set_option autoImplicit false

open Filter Topology

theorem solution {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    (hf : ZeroOneIALM.IsStronglyConvex f) : ZeroOneIALM.IsCoercive f := by
  obtain ⟨σ, hσ, hsc⟩ := hf
  set g : EuclideanSpace ℝ (Fin p) → ℝ := fun x => f x - σ / 2 * ‖x‖ ^ 2 with hgdef
  have hg : ConvexOn ℝ Set.univ g := strongConvexOn_iff_convex.mp hsc
  have hgc : Continuous g := hg.locallyLipschitz.continuous
  obtain ⟨m, hm⟩ : BddBelow (g '' Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1) :=
    (isCompact_sphere 0 1).bddBelow_image hgc.continuousOn
  have key : ∀ x, 1 ≤ ‖x‖ → ‖x‖ * (m - g 0) + g 0 ≤ g x := by
    intro x hx
    set r := ‖x‖ with hr
    have hr0 : 0 < r := by linarith
    have hy : r⁻¹ • x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin p)) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0,
        inv_mul_cancel₀ hr0.ne']
    have h1 : m ≤ g (r⁻¹ • x) := hm ⟨_, hy, rfl⟩
    have hb1 : 0 ≤ 1 - r⁻¹ := by
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ hx
    have h2 := hg.2 (Set.mem_univ 0) (Set.mem_univ x) hb1 (inv_nonneg.mpr hr0.le) (by ring)
    simp only [smul_zero, zero_add, smul_eq_mul] at h2
    have h3 : r * m ≤ r * ((1 - r⁻¹) * g 0 + r⁻¹ * g x) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hr0.le
    have h4 : r * ((1 - r⁻¹) * g 0 + r⁻¹ * g x) = (r - 1) * g 0 + g x := by
      field_simp
    nlinarith
  unfold ZeroOneIALM.IsCoercive
  rw [Filter.tendsto_atTop]
  intro b
  set c := m - g 0 with hc
  set R := 1 + 2 / σ * (|c| + |g 0| + |b|) with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 / σ * (|c| + |g 0| + |b|) := by positivity
    linarith
  filter_upwards [(tendsto_norm_cocompact_atTop).eventually_ge_atTop R] with x hx
  have hx1 : 1 ≤ ‖x‖ := hR1.trans hx
  have hk := key x hx1
  have hfx : f x = g x + σ / 2 * ‖x‖ ^ 2 := by simp only [hgdef]; ring
  rw [hfx]
  set r := ‖x‖ with hr
  have hσr : |c| + |g 0| + |b| ≤ σ / 2 * r := by
    have : σ / 2 * R = σ / 2 + (|c| + |g 0| + |b|) := by rw [hR]; field_simp
    have : σ / 2 * R ≤ σ / 2 * r := mul_le_mul_of_nonneg_left hx (by positivity)
    linarith
  have e1 : r * (|c| + |g 0| + |b|) ≤ σ / 2 * r ^ 2 := by nlinarith
  have e2 : -(r * |c|) ≤ r * c := by nlinarith [neg_abs_le c]
  have e3 : |g 0| + |b| ≤ r * (|g 0| + |b|) := by nlinarith [abs_nonneg (g 0), abs_nonneg b]
  have e4 : -|g 0| ≤ g 0 := neg_abs_le _
  have e5 : b ≤ |b| := le_abs_self b
  nlinarith
