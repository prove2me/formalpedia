-- Prove2me | solution 1 for PauliUnclonable531.Pauli.psd_blocks
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:08:29.272377+00:00
-- url     : https://prove2.me/submissions/7501e528-45d6-4521-bbb5-262c1c5b7d3d

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Operators

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Blocks

open PauliUnclonable531.Pauli

variable {A : Type} [Fintype A] [DecidableEq A]

/-- The sum/difference block matrix `[[1,1],[1,-1]]`. -/
def U2 : Op (A ⊕ A) := Matrix.fromBlocks 1 1 1 (-1)

lemma U2_conjTranspose : (U2 : Op (A ⊕ A)).conjTranspose = U2 := by
  simp [U2, Matrix.fromBlocks_conjTranspose]

lemma U2_conj (P Q R S : Op A) :
    U2 * Matrix.fromBlocks P Q R S * U2 =
      Matrix.fromBlocks (P + Q + R + S) (P - Q + R - S) (P + Q - R - S) (P - Q - R + S) := by
  simp only [U2, Matrix.fromBlocks_multiply]
  congr 1 <;> simp <;> abel

lemma diag_psd (P Q : Op A) (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    (Matrix.fromBlocks P 0 0 Q).PosSemidef := by
  open scoped MatrixOrder in
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  open scoped MatrixOrder in
  obtain ⟨T, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromBlocks S 0 0 T)
  convert h using 1
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.star_eq_conjTranspose]

end PauliUnclonable531.Pauli.Blocks

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Blocks in
theorem solution {A : Type} [Fintype A] [DecidableEq A]
    (X Y Z : Op A) (hX : X.IsHermitian) (hY : Y.IsHermitian) (hZ : Z.IsHermitian) :
    (Z.PosDef → ((Matrix.fromBlocks X Y Y Z).PosSemidef ↔ (X - Y * Z⁻¹ * Y).PosSemidef)) ∧
    ((Matrix.fromBlocks X Y Y X).PosSemidef ↔ (X - Y).PosSemidef ∧ (X + Y).PosSemidef) := by
  refine ⟨fun hZpd => ?_, ?_⟩
  · letI : Invertible Z := hZpd.isUnit.invertible
    have h := Matrix.PosDef.fromBlocks₂₂ X Y hZpd
    rwa [hY.eq] at h
  · constructor
    · intro hM
      have hc := hM.mul_mul_conjTranspose_same (U2 : Op (A ⊕ A))
      rw [U2_conjTranspose, U2_conj] at hc
      have h11 := hc.submatrix (Sum.inl : A → A ⊕ A)
      have h22 := hc.submatrix (Sum.inr : A → A ⊕ A)
      have e11 : (Matrix.fromBlocks (X + Y + Y + X) (X - Y + Y - X) (X + Y - Y - X)
          (X - Y - Y + X)).submatrix (Sum.inl : A → A ⊕ A) Sum.inl = (2 : ℝ) • (X + Y) := by
        ext i j; simp [two_smul]; ring
      have e22 : (Matrix.fromBlocks (X + Y + Y + X) (X - Y + Y - X) (X + Y - Y - X)
          (X - Y - Y + X)).submatrix (Sum.inr : A → A ⊕ A) Sum.inr = (2 : ℝ) • (X - Y) := by
        ext i j; simp [two_smul]; ring
      rw [e11] at h11
      rw [e22] at h22
      have h1 := h11.smul (show (0 : ℝ) ≤ 1/2 by norm_num)
      have h2 := h22.smul (show (0 : ℝ) ≤ 1/2 by norm_num)
      rw [smul_smul] at h1 h2
      norm_num at h1 h2
      exact ⟨h2, h1⟩
    · rintro ⟨hm, hp⟩
      have hd := (diag_psd (X + Y) (X - Y) hp hm).mul_mul_conjTranspose_same (U2 : Op (A ⊕ A))
      rw [U2_conjTranspose, U2_conj] at hd
      have hs := hd.smul (show (0 : ℝ) ≤ 1/2 by norm_num)
      convert hs using 1
      rw [Matrix.fromBlocks_smul]
      congr 1 <;> simp <;> module
