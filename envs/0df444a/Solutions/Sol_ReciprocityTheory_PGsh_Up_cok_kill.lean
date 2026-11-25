-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.cok_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:10.899836+00:00
-- url     : https://prove2.me/submissions/4285be0f-3c5e-4647-8b0c-1f6ca4dfbc68

import Definitions.Def_ReciprocityTheory_DualLattices_LenIdBStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFromRowsMulVecIff
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
private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]
    [IsDomain S] {A B : Matrix n n S} {c : S} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n S)) :
    B * A = c • (1 : Matrix n n S) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : A.det • (B * A) = A.det • (c • (1 : Matrix n n S)) := by
    calc A.det • (B * A) = (A.adjugate * A) * (B * A) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = A.adjugate * ((A * B) * A) := by simp only [Matrix.mul_assoc]
      _ = A.adjugate * (c • A) := by rw [h, Matrix.smul_mul, Matrix.one_mul]
      _ = c • (A.adjugate * A) := by rw [Matrix.mul_smul]
      _ = A.det • (c • (1 : Matrix n n S)) := by rw [Matrix.adjugate_mul]; exact smul_comm _ _ _
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa only [Matrix.smul_apply, smul_eq_mul] using mul_left_cancel₀ hdet h2
private theorem block_products_of_transpose_form_eq_smul [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R}
    {E : Matrix (Ix g) (Ix g) R} {cp : R} (hcp : cp ≠ 0) (hE : IsUnit E.det)
    (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Bt * (Eᵀ)⁻¹ * Htᵀ = cp • 1 ∧ Bt * (Eᵀ)⁻¹ * Btᵀ = 0 ∧ -(Ht * (Eᵀ)⁻¹) * Htᵀ = 0 ∧
      -(Ht * (Eᵀ)⁻¹) * Btᵀ = cp • 1 := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  have hEF : Eᵀ * (Eᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have hP : Matrix.fromCols Htᵀ Btᵀ * Matrix.fromRows (Bt * (Eᵀ)⁻¹) (-(Ht * (Eᵀ)⁻¹)) =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.sub_mul, hT1, Matrix.smul_mul, hEF]
  have hQ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero hcp hP
  rw [Matrix.fromRows_mul_fromCols] at hQ
  have h1 : (cp • (1 : Matrix (Ix g) (Ix g) R)) = Matrix.fromBlocks (cp • 1) 0 0 (cp • 1) := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, Matrix.fromBlocks_inj] at hQ
  exact hQ
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
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hπi : π (π i) = i)
    (hHt : ∀ j, Ht * εT j = (εL (π j))ᵀ * Ht) :
    ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), ∃ t, Ht *ᵥ (εT (π i) *ᵥ t) = cp • f := by
  intro f hf
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hf
  obtain ⟨-, -, -, h22⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  rw [Matrix.neg_mul, Matrix.mul_assoc] at h22
  have hHt' : Ht *ᵥ (-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y))) = cp • y := by
    rw [Matrix.mulVec_neg]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.neg_mulVec, h22, smulMV, Matrix.one_mulVec]
  generalize -((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y)) = t at hHt'
  refine ⟨t, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, hHt, hπi, ← Matrix.mulVec_mulVec, hHt', Matrix.mulVec_smul]
end ReciprocityTheory.PGsh.Up
