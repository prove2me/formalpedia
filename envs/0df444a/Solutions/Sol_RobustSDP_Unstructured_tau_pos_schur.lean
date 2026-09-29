-- Prove2me | solution 1 for RobustSDP.Unstructured.tau_pos_schur
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:47:36.334288+00:00
-- url     : https://prove2.me/submissions/dcaff6ee-9276-4d63-9a11-421b831c1a7a

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix

namespace RobustSDP.Unstructured

lemma aux_tps_rTr {m n : ℕ} (x : Fin m → ℝ) :
    (rMat (n := n) x)ᵀ * rMat (n := n) x = (1 + ∑ i, x i ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext a b
  simp only [Matrix.mul_apply, transpose_apply, rMat, of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst hab
    simp [one_apply, Fin.sum_univ_succ, sq]
  · simp [one_apply, hab, Ne.symm hab]

lemma aux_tps_schur {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) (τ : ℝ) (x : Fin m → ℝ) (hτ : 0 < τ) :
    (lmi20 Fs ρ τ x).PosSemidef ↔
      (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  have hD : (τ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ)).PosDef :=
    PosDef.one.smul hτ
  let _ : Invertible (τ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ)) :=
    ⟨τ⁻¹ • 1, by rw [smul_mul_smul_comm, inv_mul_cancel₀ hτ.ne', one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hτ.ne', one_mul, one_smul]⟩
  have hinv : (τ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ))⁻¹ = τ⁻¹ • 1 := by
    rw [← invOf_eq_nonsing_inv]
    rfl
  have hB : (ρ • (rMat (n := n) x)ᵀ)ᴴ = ρ • rMat (n := n) x := by
    simp [conjTranspose_eq_transpose_of_trivial]
  unfold lmi20
  rw [← hB, PosDef.fromBlocks₂₂ _ _ hD, hinv, hB]
  have key : ρ • (rMat (n := n) x)ᵀ * (τ⁻¹ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ)) *
      (ρ • rMat (n := n) x) = (ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, aux_tps_rTr, smul_smul]
    congr 1
    field_simp
  rw [key, sub_sub, ← add_smul]

end RobustSDP.Unstructured

open RobustSDP.Unstructured
open Matrix
open scoped Matrix.Norms.L2Operator

theorem solution {m n : ℕ} (hn : 0 < n) (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (τ : ℝ) (x : Fin m → ℝ) :
    (lmi20 Fs ρ τ x).PosSemidef ↔
      0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  classical
  constructor
  · intro h
    let p : Fin (m + 1) × Fin n := (0, ⟨0, hn⟩)
    have hτ0 : 0 ≤ τ := by
      have := h.diag_nonneg (i := Sum.inr p)
      simpa [lmi20] using this
    have hτ : 0 < τ := by
      rcases hτ0.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        have hq : star (Pi.single (Sum.inr p) 1 : Fin n ⊕ (Fin (m + 1) × Fin n) → ℝ) ⬝ᵥ
            (lmi20 Fs ρ τ x) *ᵥ Pi.single (Sum.inr p) 1 = 0 := by
          simp [lmi20, ← h1]
        have h2 := (h.dotProduct_mulVec_zero_iff _).1 hq
        have h3 := congrFun h2 (Sum.inl ⟨0, hn⟩)
        simp [lmi20, rMat, p] at h3
        exact hρ.ne' h3
    exact ⟨hτ, (aux_tps_schur Fs ρ τ x hτ).1 h⟩
  · rintro ⟨hτ, h⟩
    exact (aux_tps_schur Fs ρ τ x hτ).2 h
