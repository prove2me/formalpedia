-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ht_cp_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:59.284181+00:00
-- url     : https://prove2.me/submissions/af523d93-d67d-4bc4-8f6f-34fe7aeba96f

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
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
open ReciprocityTheory.PGsh.L2
private lemma mul_eq_smul_one_comm_of_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    [IsDomain R] {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • 1) :
    B * A = c • 1 := by
  have hdet : A.det * B.det = c ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have h1 : A * (B * A - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul, sub_self]
  have h2 : A.det • (B * A - c • 1) = 0 := by
    rw [← Matrix.one_mul (B * A - c • 1), ← Matrix.smul_mul, ← Matrix.adjugate_mul A,
      Matrix.mul_assoc, h1, Matrix.mul_zero]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h3
  have h4 := (mul_eq_zero.1 h3).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h4
  exact h4
section HTDfacts
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
end HTDfacts
section Unram
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
end Unram
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {g : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (E : Matrix (Ix g) (Ix g) R) (cp : R) (hEt : Eᵀ = -E) (hdiag : ∀ i, E i i = 0)
    (hdet : IsUnit E.det) (hc : cp ≠ 0) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    ∀ f : Fin g → R, ∃ t, Ht *ᵥ t = cp • f := by
  intro f
  classical
  have hΨΦ : E⁻¹ * Matrix.fromCols Btᵀ (-Htᵀ) * Matrix.fromRows Ht Bt =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.neg_mul, ← sub_eq_add_neg, hform,
      Matrix.mul_smul, Matrix.nonsing_inv_mul E hdet]
  have hsq := mul_eq_smul_one_comm_of_ne_zero (n := Ix g) hc hΨΦ
  refine ⟨(E⁻¹ * Matrix.fromCols Btᵀ (-Htᵀ)) *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R), ?_⟩
  funext k
  have h5 : (cp • (1 : Matrix (Ix g) (Ix g) R)) *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R) =
      cp • (Sum.elim f 0 : Fin g ⊕ Fin g → R) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h1 := congrFun (congrArg (fun M => M *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R)) hsq) (Sum.inl k)
  rw [← Matrix.mulVec_mulVec, h5] at h1
  exact h1
end ReciprocityTheory.PGsh.Up
