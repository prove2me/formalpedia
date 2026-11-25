-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.exists_fromRows_mulVec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:03:43.658058+00:00
-- url     : https://prove2.me/submissions/5a01a94d-f4e3-4543-95a8-104aac830af0

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hb_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g : ℕ}
private lemma smulMV {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R) (v : μ → R) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.mul_sum, mul_assoc]
variable {m : ℕ}
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R] {g : ℕ}
variable {m : ℕ}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hHt : Ht * εT i = (εL (π i))ᵀ * Ht)
    (hBt : Bt * εT i = εL i * Bt) (x : Fin g → R) (hx : εL i *ᵥ x = x) :
    (∃ t, fromRows Ht Bt *ᵥ (εT i *ᵥ t) = Sum.elim (0 : Fin g → R) x) ↔
      ∃ z, Htᵀ *ᵥ x = cp • z := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  constructor
  · rintro ⟨t, ht⟩
    rw [Matrix.fromRows_mulVec] at ht
    have h1 : Ht *ᵥ (εT i *ᵥ t) = 0 := funext fun k => by simpa using congrFun ht (Sum.inl k)
    have h2 : Bt *ᵥ (εT i *ᵥ t) = x := funext fun k => by simpa using congrFun ht (Sum.inr k)
    refine ⟨Eᵀ *ᵥ (εT i *ᵥ t), ?_⟩
    rw [← smulMV, ← hT1, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
      h2, Matrix.mulVec_zero, sub_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨hHF, hBF⟩ := hb_facts hcp hE hform
    have hs1 : Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = 0 := by
      have h : cp • (Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = 0 := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hHF, Matrix.zero_mulVec]
      exact (smul_eq_zero.mp h).resolve_left hcp
    have hs2 : Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = x := by
      have h : cp • (Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = cp • x := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hBF, smulMV, Matrix.one_mulVec]
      exact smul_right_injective _ hcp h
    generalize (Eᵀ)⁻¹ *ᵥ z = s at hs1 hs2
    have e1 : Ht *ᵥ (εT i *ᵥ s) = 0 := by
      rw [Matrix.mulVec_mulVec, hHt, ← Matrix.mulVec_mulVec, hs1, Matrix.mulVec_zero]
    have e2 : Bt *ᵥ (εT i *ᵥ s) = x := by
      rw [Matrix.mulVec_mulVec, hBt, ← Matrix.mulVec_mulVec, hs2, hx]
    exact ⟨s, by rw [Matrix.fromRows_mulVec, e1, e2]⟩
end ReciprocityTheory.PGsh.Up
