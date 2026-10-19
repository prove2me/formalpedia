-- Prove2me | solution 1 for QAlgorithms.Childs.effective_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:52:44.763529+00:00
-- url     : https://prove2.me/submissions/6283650e-e2a9-41a5-b64e-9ad6bb979012

import Definitions.Def_QAlgorithms_Defs_Adversary
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Analysis.InnerProductSpace.Subspace

set_option autoImplicit false

open QAlgorithms
open scoped ComplexConjugate

private lemma phase_distance (θ : ℝ) : ‖1 - Complex.exp (θ * Complex.I)‖ ≤ |θ| := by
  rw [norm_sub_rev, mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs]
  norm_num
  have h := Real.abs_sin_le_abs (x := θ / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

private lemma restricted_displacement {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E →ₗᵢ[ℂ] E) (S : Set ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hunit : ∀ μ ∈ S, ‖μ‖ = 1) (hclose : ∀ μ ∈ S, ‖1 - μ‖ ≤ c)
    (x : E) (hx : x ∈ ⨆ μ : S, Module.End.eigenspace U.toLinearMap μ) :
    ‖x - U x‖ ≤ c * ‖x‖ := by
  classical
  let V : S → Submodule ℂ E := fun μ => Module.End.eigenspace U.toLinearMap μ
  have orth : OrthogonalFamily ℂ (fun μ => V μ) (fun μ => (V μ).subtypeₗᵢ) := by
    intro μ ν hne v w
    have hv : U (v : E) = (μ : ℂ) • (v : E) := Module.End.mem_eigenspace_iff.mp v.property
    have hw : U (w : E) = (ν : ℂ) • (w : E) := Module.End.mem_eigenspace_iff.mp w.property
    have hi := U.inner_map_map (v : E) (w : E)
    rw [hv, hw, inner_smul_left, inner_smul_right] at hi
    have hm : (μ : ℂ) * conj (μ : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit μ μ.property]
      norm_num
    have he : (ν : ℂ) * inner ℂ (v : E) (w : E) =
        (μ : ℂ) * inner ℂ (v : E) (w : E) := by
      have := congrArg (fun z : ℂ => (μ : ℂ) * z) hi
      calc
        (ν : ℂ) * inner ℂ (v : E) (w : E) =
            ((μ : ℂ) * conj (μ : ℂ)) * ((ν : ℂ) * inner ℂ (v : E) (w : E)) := by rw [hm, one_mul]
        _ = (μ : ℂ) * inner ℂ (v : E) (w : E) := by linear_combination this
    by_contra hn
    exact hne (Subtype.ext ((mul_right_cancel₀ hn he).symm))
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp V x).mp hx
  let l : ∀ μ, V μ := fun μ => ⟨f μ, hf μ⟩
  let d : ∀ μ, V μ := fun μ => (1 - (μ : ℂ)) • l μ
  have hs : (∑ μ ∈ f.support, ((l μ : V μ) : E)) = x := hsum
  have hd : (∑ μ ∈ f.support, ((d μ : V μ) : E)) = x - U x := by
    rw [← hs, map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro μ hμ
    have he : U (l μ : E) = (μ : ℂ) • (l μ : E) :=
      Module.End.mem_eigenspace_iff.mp (l μ).property
    simp [d, he, sub_smul]
  have hb : ‖x - U x‖ ^ 2 ≤ c ^ 2 * ‖x‖ ^ 2 := by
    have hl := orth.norm_sum l f.support
    have hd' := orth.norm_sum d f.support
    change ‖∑ μ ∈ f.support, ((l μ : V μ) : E)‖ ^ 2 = _ at hl
    change ‖∑ μ ∈ f.support, ((d μ : V μ) : E)‖ ^ 2 = _ at hd'
    rw [hs] at hl
    rw [hd] at hd'
    rw [hd', hl, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro μ hμ
    dsimp [d]
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [hclose μ μ.property, norm_nonneg (1 - (μ : ℂ))]) (sq_nonneg _)
  nlinarith [norm_nonneg (x - U x), mul_nonneg hc (norm_nonneg x)]

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (K L : Submodule ℂ E) (ω : ℝ) (hω : 0 ≤ ω) (ϕ : E)
    (hϕ : ‖ϕ‖ = 1) (hΔ : L.starProjection ϕ = 0) :
    ‖eigenProjection (reflProduct K L)
        {μ : ℂ | ∃ θ : ℝ, |θ| < ω ∧ μ = Complex.exp (θ * Complex.I)}
        (K.starProjection ϕ)‖ ≤ ω / 2 := by
  classical
  let U : E →ₗᵢ[ℂ] E := (L.reflection.trans K.reflection).toLinearIsometry
  let S : Set ℂ := {μ | ∃ θ : ℝ, |θ| < ω ∧ μ = Complex.exp (θ * Complex.I)}
  let W : Submodule ℂ E := ⨆ μ ∈ S, Module.End.eigenspace U.toLinearMap μ
  let p := K.starProjection ϕ
  let y := W.starProjection p
  change ‖y‖ ≤ ω / 2
  have hy : y ∈ W := W.starProjection_apply_mem p
  have hbound : ‖y - U y‖ ≤ ω * ‖y‖ := by
    apply restricted_displacement U S ω hω
    · rintro μ ⟨θ, hθ, rfl⟩
      exact Complex.norm_exp_ofReal_mul_I θ
    · rintro μ ⟨θ, hθ, rfl⟩
      exact (phase_distance θ).trans hθ.le
    · simpa only [iSup_subtype] using hy
  have huphi : U ϕ = ϕ - 2 • p := by
    change K.reflection (L.reflection ϕ) = ϕ - 2 • K.starProjection ϕ
    have hL : L.reflection ϕ = -ϕ := by
      rw [Submodule.reflection_apply, hΔ, smul_zero, zero_sub]
    rw [hL, map_neg, Submodule.reflection_apply]
    abel
  have hip : inner ℂ y p = inner ℂ y y := by
    calc
      inner ℂ y p = inner ℂ (W.starProjection y) p := by
        rw [W.starProjection_eq_self_iff.mpr hy]
      _ = inner ℂ y (W.starProjection p) := W.inner_starProjection_left_eq_right y p
      _ = inner ℂ y y := rfl
  have hid : inner ℂ (y - U y) (U ϕ) = -(2 : ℂ) * inner ℂ y y := by
    rw [inner_sub_left, U.inner_map_map, huphi, inner_sub_right,
      two_smul, inner_add_right, hip]
    ring
  have heq : ‖inner ℂ (y - U y) (U ϕ)‖ = 2 * ‖y‖ ^ 2 := by
    rw [hid, norm_mul, norm_neg, inner_self_eq_norm_sq_to_K]
    simp
  have hcs := norm_inner_le_norm (𝕜 := ℂ) (y - U y) (U ϕ)
  rw [heq, U.norm_map, hϕ, mul_one] at hcs
  have hn := norm_nonneg y
  nlinarith
