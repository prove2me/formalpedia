-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.cond_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:33.97038+00:00
-- url     : https://prove2.me/submissions/42d4493b-e0ee-4cab-b2a0-c69d8cea4ab8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution (A C : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (hε : ε * ε = 1)
    (h : Aᵀ * C.map c + (ε : R) • (Cᵀ * A.map c) = 0) (ε₁ : ℤ) :
    ((ε₁ : R) • (C * A⁻¹))ᵀ + (ε : R) • ((ε₁ : R) • (C * A⁻¹)).map c = 0 := by
  have hP : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hQdet : (A.map c).det = c A.det := (RingHom.map_det c A).symm
  have hQ : IsUnit (A.map c).det := by rw [hQdet]; exact hA.map c
  have hinv : (A.map c)⁻¹ = (A⁻¹).map c := Matrix.inv_eq_left_inv (by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one c (map_zero c) (map_one c)])
  have hεR : (ε : R) * (ε : R) = 1 := by rw [← Int.cast_mul, hε, Int.cast_one]
  have key : (C * A⁻¹)ᵀ + (ε : R) • (C * A⁻¹).map c = 0 := by
    rw [Matrix.transpose_mul, Matrix.map_mul, Matrix.transpose_nonsing_inv, ← hinv]
    have hcancel : ∀ Z : Matrix (Fin n) (Fin n) R, Aᵀ * Z * A.map c = 0 → Z = 0 := by
      intro Z hZ
      calc Z = (Aᵀ)⁻¹ * (Aᵀ * Z * A.map c) * (A.map c)⁻¹ := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul,
              Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
        _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
    apply hcancel
    have e1 : Aᵀ * ((Aᵀ)⁻¹ * Cᵀ) * A.map c = Cᵀ * A.map c := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.one_mul]
    have e2 : Aᵀ * (C.map c * (A.map c)⁻¹) * A.map c = Aᵀ * C.map c := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, e2,
      eq_neg_of_add_eq_zero_left h, smul_neg, smul_smul, hεR, one_smul, add_neg_cancel]
  have hc1 : c (ε₁ : R) = (ε₁ : R) := map_intCast c ε₁
  rw [Matrix.transpose_smul, Matrix.map_smul' c _ _ (map_mul c), hc1, smul_comm (ε : R) (ε₁ : R), ← smul_add,
    key, smul_zero]
end PositivityTheory.SiegelWeilFormula.KAway
