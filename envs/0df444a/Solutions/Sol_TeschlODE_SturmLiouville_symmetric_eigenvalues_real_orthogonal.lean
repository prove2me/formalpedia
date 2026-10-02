-- Prove2me | solution 1 for TeschlODE.SturmLiouville.symmetric_eigenvalues_real_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:50:54.045895+00:00
-- url     : https://prove2.me/submissions/39a11bbe-9a7a-4abd-bd8b-d8a24c3170f7

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsSymmetricOp

set_option autoImplicit false

open TeschlODE.SturmLiouville in
theorem TeschlODE_sym_eig_real_aux {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (D : Submodule ℂ E) (A : D →ₗ[ℂ] E) (hA : IsSymmetricOp D A)
    (z : ℂ) (u : D) (hu : u ≠ 0) (h : A u = z • (u : E)) : (starRingEnd ℂ) z = z := by
  have h1 := hA.2 u u
  rw [h, inner_smul_right, inner_smul_left] at h1
  have hne : inner ℂ (u : E) (u : E) ≠ 0 := by
    rw [inner_self_ne_zero]
    intro h0; exact hu (Subtype.ext h0)
  exact (mul_right_cancel₀ hne h1).symm

open TeschlODE.SturmLiouville in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (D : Submodule ℂ E) (A : D →ₗ[ℂ] E) (hA : IsSymmetricOp D A) :
    (∀ (z : ℂ) (u : D), u ≠ 0 → A u = z • (u : E) → z.im = 0) ∧
    (∀ (z₁ z₂ : ℂ) (u₁ u₂ : D), u₁ ≠ 0 → u₂ ≠ 0 → A u₁ = z₁ • (u₁ : E) →
      A u₂ = z₂ • (u₂ : E) → z₁ ≠ z₂ → inner ℂ (u₁ : E) (u₂ : E) = 0) := by
  refine ⟨fun z u hu h => ?_, fun z₁ z₂ u₁ u₂ hu₁ hu₂ h₁ h₂ hz => ?_⟩
  · exact Complex.conj_eq_iff_im.mp (TeschlODE_sym_eig_real_aux D A hA z u hu h)
  · have hc2 := TeschlODE_sym_eig_real_aux D A hA z₂ u₂ hu₂ h₂
    have h1 := hA.2 u₁ u₂
    rw [h₁, h₂, inner_smul_right, inner_smul_left, hc2] at h1
    have h0 : inner ℂ (u₂ : E) (u₁ : E) = 0 := by
      have : (z₁ - z₂) * inner ℂ (u₂ : E) (u₁ : E) = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hz)
    rw [← inner_conj_symm, h0, map_zero]
