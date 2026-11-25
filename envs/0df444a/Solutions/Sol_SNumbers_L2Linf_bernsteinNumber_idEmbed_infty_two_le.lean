-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_idEmbed_infty_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:08:07.191171+00:00
-- url     : https://prove2.me/submissions/ec9ab8c8-3a2e-4dca-a80b-522d31480474

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_exists_mem_apply_eq_norm_sq
public import Theorems.Thm_SNumbers_L2Linf_sum_sum_norm_sq_apply
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_gainOnSubspace_le_div
public import Theorems.Thm_SNumbers_gainOnSubspace_nonneg
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) n ≤ Real.sqrt (N / (n + 1)) := by
  refine Real.sSup_le ?_ (Real.sqrt_nonneg _)
  rintro _ ⟨M, hM_rank, rfl⟩
  set c := gainOnSubspace (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) M with hc_def
  have hc0 : 0 ≤ c := gainOnSubspace_nonneg _ _
  -- the same subspace, inside `ℓ₂ᴺ`
  set E : PiLp ∞ (fun _ : Fin N => 𝕜) ≃ₗ[𝕜] PiLp 2 (fun _ : Fin N => 𝕜) :=
    (WithLp.linearEquiv ∞ 𝕜 (Fin N → 𝕜)).trans (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm
    with hE
  set M₂ : Submodule 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜)) :=
    M.map (E : PiLp ∞ (fun _ : Fin N => 𝕜) →ₗ[𝕜] PiLp 2 (fun _ : Fin N => 𝕜)) with hM₂
  have hd : Module.finrank 𝕜 M₂ = n + 1 := by
    rw [hM₂, LinearEquiv.finrank_map_eq, Module.finrank_eq_of_rank_eq hM_rank]
  set b := stdOrthonormalBasis 𝕜 M₂ with hb
  obtain ⟨s, hs⟩ : ∃ s : Fin N → ℝ,
      s = fun k => ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := ⟨_, rfl⟩
  have hs_apply : ∀ k, s k = ∑ i, ‖(b i : PiLp 2 (fun _ : Fin N => 𝕜)) k‖ ^ 2 := by
    intro k; rw [hs]
  -- each coordinate: `c² · s k ≤ 1`
  have hkey : ∀ k, c ^ 2 * s k ≤ 1 := by
    intro k
    have hs0 : 0 ≤ s k := by rw [hs_apply]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases hs0.eq_or_lt with hsk | hsk
    · rw [← hsk, mul_zero]; exact zero_le_one
    obtain ⟨x, hxM₂, hxk, hxnorm⟩ := exists_mem_apply_eq_norm_sq b k
    rw [← hs_apply] at hxk hxnorm
    obtain ⟨y, hyM, hyx⟩ := Submodule.mem_map.mp hxM₂
    -- `y ∈ M` and `x ∈ M₂` have the same coordinates
    have hcoord : ∀ i, y i = x i := fun i => by rw [← hyx]; rfl
    have hid : idEmbed (𝕜 := 𝕜) (m := N) 2 ∞ y = x := by rw [← hyx]; rfl
    have hy0 : y ≠ 0 := by
      intro h
      have hx0 : x k = 0 := by rw [← hcoord k, h, PiLp.zero_apply]
      rw [hxk, RCLike.ofReal_eq_zero] at hx0
      exact hsk.ne' hx0
    have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    -- `s k = |x k| = |y k| ≤ ‖y‖_∞`
    have hyk : s k ≤ ‖y‖ := by
      calc s k = ‖x k‖ := by rw [hxk, RCLike.norm_ofReal, abs_of_nonneg hs0]
        _ = ‖y k‖ := by rw [hcoord]
        _ ≤ ‖y‖ := PiLp.norm_apply_le y k
    -- the gain on `M` is at most `‖x‖₂ / ‖y‖_∞`
    have hgain : c * ‖y‖ ≤ ‖x‖ := by
      have h := gainOnSubspace_le_div (S := idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) hyM hy0
      rw [hid, le_div_iff₀ hypos] at h
      exact h
    have h1 : c * s k ≤ ‖x‖ :=
      (mul_le_mul_of_nonneg_left hyk hc0).trans hgain
    have h2 : (c * s k) ^ 2 ≤ s k := by
      calc (c * s k) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = s k := hxnorm
    have h3 : c ^ 2 * s k * s k ≤ 1 * s k := by nlinarith [h2]
    exact le_of_mul_le_mul_right h3 hsk
  -- sum over the coordinates
  have hsum : ∑ k, s k = n + 1 := by
    simp only [hs_apply]
    rw [sum_sum_norm_sq_apply b, Fintype.card_fin, hd, Nat.cast_add, Nat.cast_one]
  have hmain : c ^ 2 * (n + 1) ≤ N := by
    calc c ^ 2 * (n + 1) = ∑ k, c ^ 2 * s k := by rw [← Finset.mul_sum, hsum]
      _ ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ => hkey k
      _ = N := by simp
  rw [Real.le_sqrt hc0 (by positivity), le_div_iff₀ (by positivity)]
  exact hmain
end SNumbers.L2Linf
