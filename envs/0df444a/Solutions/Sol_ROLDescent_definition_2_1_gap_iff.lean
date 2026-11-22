-- Prove2me | solution 1 for ROLDescent.definition_2_1_gap_iff
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:10:00.824674+00:00
-- url     : https://prove2.me/submissions/b31d10ba-9446-4ed8-acbb-574acf71d73a

import Mathlib
import Definitions.Def_ROLDescent_specGap

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ROLDescent
open scoped InnerProductSpace

lemma gap_infDist_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (N : Submodule ℂ E) (f : E) :
    Metric.infDist f (N : Set E) = ‖f - N.starProjection f‖ := by
  apply le_antisymm
  · simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (N.starProjection_apply_mem f))
  · apply (Metric.le_infDist (show (N : Set E).Nonempty from ⟨0,N.zero_mem⟩)).mpr
    intro y hy
    have hp : N.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
    have he : Nᗮ.starProjection (f - y) = f - N.starProjection f := by
      rw [Submodule.starProjection_orthogonal_val, map_sub, hp]
      abel
    simpa only [he, dist_eq_norm] using Nᗮ.norm_starProjection_apply_le (f - y)

lemma gap_energy_projection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →L[ℂ] E) (hA : A.IsPositive) (f : E) :
    RCLike.re ⟪f - (LinearMap.ker (A : E →ₗ[ℂ] E)).starProjection f,
      A (f - (LinearMap.ker (A : E →ₗ[ℂ] E)).starProjection f)⟫_ℂ =
        RCLike.re ⟪f,A f⟫_ℂ := by
  let N := LinearMap.ker (A : E →ₗ[ℂ] E)
  have hp : A (N.starProjection f) = 0 :=
    N.starProjection_apply_mem f
  have hc : ⟪N.starProjection f,A f⟫_ℂ = 0 := by
    rw [← hA.inner_left_eq_inner_right, hp, inner_zero_left]
  change RCLike.re ⟪f - N.starProjection f,A (f - N.starProjection f)⟫_ℂ = _
  rw [map_sub, hp, sub_zero, inner_sub_left, hc, sub_zero]

end ROLDescent
open ROLDescent
open scoped InnerProductSpace

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (A : E →L[ℂ] E) (hA : A.IsPositive)
    (hN : (LinearMap.ker (A : E →ₗ[ℂ] E))ᗮ ≠ ⊥) (γ : ℝ) (hγ : 0 ≤ γ) :
    γ ≤ specGap A ↔ ∀ f : E,
      γ * Metric.infDist f (LinearMap.ker (A : E →ₗ[ℂ] E) : Set E) ^ 2 ≤ RCLike.re ⟪f, A f⟫_ℂ := by
  let N := LinearMap.ker (A : E →ₗ[ℂ] E)
  let S : Set ℝ := {r | ∃ f ∈ Nᗮ, f ≠ 0 ∧ r = RCLike.re ⟪f,A f⟫_ℂ / ‖f‖^2}
  have hbelow : BddBelow S := by
    refine ⟨0,?_⟩
    rintro r ⟨f,hf,hf0,rfl⟩
    exact div_nonneg (hA.re_inner_nonneg_right f) (sq_nonneg _)
  have hnonempty : S.Nonempty := by
    obtain ⟨f,hf,hf0⟩ := (Submodule.ne_bot_iff Nᗮ).mp hN
    exact ⟨_,f,hf,hf0,rfl⟩
  change γ ≤ sInf S ↔ ∀ f : E, γ * Metric.infDist f (N : Set E)^2 ≤ _
  constructor
  · intro hgap f
    let g := f - N.starProjection f
    have hg : g ∈ Nᗮ := N.sub_starProjection_mem_orthogonal f
    rw [gap_infDist_projection N f]
    change γ * ‖g‖^2 ≤ _
    by_cases hg0 : g = 0
    · rw [hg0,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
      exact hA.re_inner_nonneg_right f
    · have hmem : RCLike.re ⟪g,A g⟫_ℂ / ‖g‖^2 ∈ S := ⟨g,hg,hg0,rfl⟩
      have hr := hgap.trans (csInf_le hbelow hmem)
      have hp : 0 < ‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg0)
      have hb := (le_div_iff₀ hp).mp hr
      have he := gap_energy_projection A hA f
      change RCLike.re ⟪g,A g⟫_ℂ = _ at he
      rwa [he] at hb
  · intro h
    apply le_csInf hnonempty
    rintro r ⟨f,hf,hf0,rfl⟩
    have hp : N.starProjection f = 0 := by
      change f ∈ N.starProjection.ker
      rw [Submodule.ker_starProjection]
      exact hf
    have hi : Metric.infDist f (N : Set E) = ‖f‖ := by
      rw [gap_infDist_projection, hp, sub_zero]
    have hb := h f
    rw [hi] at hb
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf0))).mpr hb

