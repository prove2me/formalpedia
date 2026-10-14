-- Prove2me | solution 1 for RobinsonSR.NLP.schur_eq_and_symm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:46:44.989202+00:00
-- url     : https://prove2.me/submissions/6f4b281b-4402-4518-b2af-2f6673ed9c2d

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix


namespace RobinsonSR.NLP

lemma kkt_mul_rows {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ)
    (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ) :
    kktMatrix Q H Gp * Matrix.fromRows V (Matrix.fromRows A B) =
      Matrix.fromRows (Q * V + Hᵀ * A + Gpᵀ * B) (Matrix.fromRows (-H * V) (-Gp * V)) := by
  ext i j
  rcases i with i | i | i <;>
    simp [kktMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
      Matrix.add_apply, add_assoc, Matrix.neg_apply, Finset.sum_neg_distrib]

lemma zero_mul_rows {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    (G0 : Matrix ιs ιn ℝ)
    (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ) :
    zeroRowBlock (ιq := ιq) (ιr := ιr) G0 * Matrix.fromRows V (Matrix.fromRows A B) = G0 * V := by
  ext i j
  simp [zeroRowBlock, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]

lemma zero_transpose {ιn ιq ιr ιs : Type*} (G0 : Matrix ιs ιn ℝ) :
    (zeroRowBlock (ιq := ιq) (ιr := ιr) G0)ᵀ = Matrix.fromRows G0ᵀ (Matrix.fromRows 0 0) := by
  ext i j
  rcases i with i | i | i <;> simp [zeroRowBlock, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr]

theorem schur_core {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hK : (kktMatrix Q H Gp).det ≠ 0) (hQ : Q.IsSymm) :
    (∃! VAB : Matrix ιn ιs ℝ × Matrix ιq ιs ℝ × Matrix ιr ιs ℝ,
        Q * VAB.1 + Hᵀ * VAB.2.1 + Gpᵀ * VAB.2.2 = G0ᵀ ∧ -H * VAB.1 = 0 ∧ -Gp * VAB.1 = 0) ∧
    (∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
        Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ → -H * V = 0 → -Gp * V = 0 →
          schurS Q H Gp G0 = G0 * V ∧ schurS Q H Gp G0 = Vᵀ * Q * V) ∧
    (schurS Q H Gp G0).IsSymm := by
  set K := kktMatrix Q H Gp with hKdef
  have hu : IsUnit K.det := isUnit_iff_ne_zero.mpr hK
  set Z := zeroRowBlock (ιq := ιq) (ιr := ιr) G0 with hZ
  -- characterization
  have key : ∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
      (Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ ∧ -H * V = 0 ∧ -Gp * V = 0) ↔
        Matrix.fromRows V (Matrix.fromRows A B) = K⁻¹ * Zᵀ := by
    intro V A B
    constructor
    · rintro ⟨h1, h2, h3⟩
      have : K * Matrix.fromRows V (Matrix.fromRows A B) = Zᵀ := by
        rw [hKdef, kkt_mul_rows, h1, h2, h3, hZ, zero_transpose]
      rw [← this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    · intro h
      have : K * Matrix.fromRows V (Matrix.fromRows A B) = Zᵀ := by
        rw [h, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      rw [hKdef, kkt_mul_rows, hZ, zero_transpose] at this
      simp only [Matrix.fromRows_ext_iff] at this
      exact ⟨this.1, this.2.1, this.2.2⟩
  have hS : ∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
      Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ → -H * V = 0 → -Gp * V = 0 →
        schurS Q H Gp G0 = G0 * V ∧ schurS Q H Gp G0 = Vᵀ * Q * V := by
    intro V A B h1 h2 h3
    have hW := (key V A B).1 ⟨h1, h2, h3⟩
    have e1 : schurS Q H Gp G0 = G0 * V := by
      unfold schurS
      rw [← hZ, ← hKdef, Matrix.mul_assoc, ← hW, hZ, zero_mul_rows]
    refine ⟨e1, ?_⟩
    rw [e1]
    have hHV : H * V = 0 := by simpa [Matrix.neg_mul] using h2
    have hGV : Gp * V = 0 := by simpa [Matrix.neg_mul] using h3
    have : G0 = (Q * V + Hᵀ * A + Gpᵀ * B)ᵀ := by rw [h1, Matrix.transpose_transpose]
    rw [this]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.add_mul, hQ.eq]
    rw [Matrix.mul_assoc Aᵀ, hHV, Matrix.mul_assoc Bᵀ, hGV]
    simp [Matrix.mul_assoc]
  -- existence
  set W := K⁻¹ * Zᵀ with hWdef
  let V : Matrix ιn ιs ℝ := Matrix.of fun i j => W (Sum.inl i) j
  let A : Matrix ιq ιs ℝ := Matrix.of fun i j => W (Sum.inr (Sum.inl i)) j
  let B : Matrix ιr ιs ℝ := Matrix.of fun i j => W (Sum.inr (Sum.inr i)) j
  have hW : Matrix.fromRows V (Matrix.fromRows A B) = W := by
    ext i j; rcases i with i | i | i <;> simp only [V, A, B, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.of_apply]
  have hsol := (key V A B).2 hW
  refine ⟨⟨(V, A, B), hsol, ?_⟩, hS, ?_⟩
  · rintro ⟨V', A', B'⟩ h'
    have h2 := (key V' A' B').1 h'
    rw [← hW] at h2
    simp only [Matrix.fromRows_ext_iff] at h2
    obtain ⟨e1, e2, e3⟩ := h2
    simp [e1, e2, e3]
  · obtain ⟨_, e⟩ := hS V A B hsol.1 hsol.2.1 hsol.2.2
    rw [Matrix.IsSymm, e]
    simp [Matrix.transpose_mul, hQ.eq, Matrix.mul_assoc]

end RobinsonSR.NLP

open RobinsonSR.NLP


theorem solution {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hK : (kktMatrix Q H Gp).det ≠ 0) (hQ : Q.IsSymm) :
    (∃! VAB : Matrix ιn ιs ℝ × Matrix ιq ιs ℝ × Matrix ιr ιs ℝ,
        Q * VAB.1 + Hᵀ * VAB.2.1 + Gpᵀ * VAB.2.2 = G0ᵀ ∧ -H * VAB.1 = 0 ∧ -Gp * VAB.1 = 0) ∧
    (∀ (V : Matrix ιn ιs ℝ) (A : Matrix ιq ιs ℝ) (B : Matrix ιr ιs ℝ),
        Q * V + Hᵀ * A + Gpᵀ * B = G0ᵀ → -H * V = 0 → -Gp * V = 0 →
          schurS Q H Gp G0 = G0 * V ∧ schurS Q H Gp G0 = Vᵀ * Q * V) ∧
    (schurS Q H Gp G0).IsSymm := by
  exact schur_core Q H Gp G0 hK hQ
