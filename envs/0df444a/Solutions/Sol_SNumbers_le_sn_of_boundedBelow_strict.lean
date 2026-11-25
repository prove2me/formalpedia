-- Prove2me | solution 1 for SNumbers.le_sn_of_boundedBelow_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:55:43.121892+00:00
-- url     : https://prove2.me/submissions/8f551674-c5f5-43eb-8197-0bd429b94e36

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜}
    (hs : IsStrictSNumberSequence s) (hinj : Injective s)
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (hE : n < Module.finrank 𝕜 E) {c : ℝ} (hc : 0 < c)
    (f : E →L[𝕜] F) (hf : ∀ x, c * ‖x‖ ≤ ‖f x‖) :
    c ≤ s f n := by
  -- `f` is injective, being bounded below by `c > 0`.
  have hf_inj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hpos : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h := hf (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h
    exact absurd h (not_le.2 (mul_pos hc hpos))
  -- Corestrict `f` to its range `V := range f ⊆ F`.
  set V : Submodule 𝕜 F := LinearMap.range (f : E →ₗ[𝕜] F) with hV
  have hmem : ∀ x, f x ∈ V := fun x => ⟨x, rfl⟩
  set f₀ : E →L[𝕜] V := f.codRestrict V hmem with hf₀_def
  -- `f₀` is a linear bijection onto `V`.
  have hf₀_inj : Function.Injective f₀ := fun a b hab =>
    hf_inj (congrArg Subtype.val hab)
  have hf₀_surj : Function.Surjective f₀ := by
    rintro ⟨z, x, rfl⟩
    exact ⟨x, Subtype.ext rfl⟩
  have hbij : Function.Bijective (f₀ : E →ₗ[𝕜] V) := ⟨hf₀_inj, hf₀_surj⟩
  set e : E ≃ₗ[𝕜] V := LinearEquiv.ofBijective (f₀ : E →ₗ[𝕜] V) hbij with he_def
  have he_apply : ∀ x, e x = f₀ x := fun x => rfl
  -- The algebraic inverse `e.symm` is bounded by `1/c`; upgrade it to a CLM `g`.
  have hbound : ∀ v : V, ‖e.symm v‖ ≤ (1 / c) * ‖v‖ := by
    intro v
    have hfx : f (e.symm v) = (v : F) := by
      have h2 : f₀ (e.symm v) = v := by rw [← he_apply]; exact e.apply_symm_apply v
      exact congrArg Subtype.val h2
    have h3 := hf (e.symm v)
    rw [hfx] at h3
    have hnorm : ‖(v : F)‖ = ‖v‖ := rfl
    rw [hnorm] at h3
    rw [show (1 / c) * ‖v‖ = ‖v‖ / c from by ring, le_div_iff₀ hc, mul_comm]
    exact h3
  set g : V →L[𝕜] E := (e.symm : V →ₗ[𝕜] E).mkContinuous (1 / c) hbound with hg_def
  have hg_norm : ‖g‖ ≤ 1 / c := by
    rw [hg_def]; exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  -- `g ∘ f₀ = id_E`.
  have hgf : g.comp f₀ = ContinuousLinearMap.id 𝕜 E := by
    ext x
    have : g (f₀ x) = x := by
      rw [hg_def, LinearMap.mkContinuous_apply]; exact e.symm_apply_apply x
    simpa using this
  -- `f = ι_V ∘ f₀` with `ι_V` a metric injection ⟹ `sₙ(f) = sₙ(f₀)`.
  have hmetric : IsMetricInjection (V.subtypeL) := fun v => rfl
  have hcomp : V.subtypeL.comp f₀ = f := by ext x; rfl
  have h_inj_eq : s f n = s f₀ n := by
    rw [← hcomp]; exact hinj f₀ V.subtypeL hmetric n
  -- Ideal property against `g = f₀⁻¹` and strict normalisation `sₙ(id_E) = 1`.
  have h_ideal := hs.ideal (ContinuousLinearMap.id 𝕜 E) f₀ g n
  rw [ContinuousLinearMap.comp_id, hgf,
    hs.strictly_normalised_at_id n (Module.lt_rank_of_lt_finrank hE)] at h_ideal
  have hsn : 0 ≤ s f₀ n := hs.nonneg f₀ n
  have hidle : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := norm_id_le
  have h1 : (1 : ℝ) ≤ ‖g‖ * s f₀ n := by
    nlinarith [h_ideal,
      mul_nonneg (mul_nonneg (norm_nonneg g) hsn) (sub_nonneg.mpr hidle)]
  have h2 : c * ‖g‖ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hg_norm hc.le
    rwa [mul_one_div, div_self hc.ne'] at hh
  have key : c ≤ s f₀ n := by
    nlinarith [h1, h2, hsn, hc.le, mul_nonneg hc.le (norm_nonneg g)]
  rw [h_inj_eq]; exact key
end SNumbers
