-- Prove2me | solution 1 for TegmarkDimensionality.field_equation_type_by_signature
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:57:46.96732+00:00
-- url     : https://prove2.me/submissions/228687d4-3972-40e1-b1a5-6633199f0f7a

import Mathlib
import Definitions.Def_tegmark_pde_classification

set_option autoImplicit false

namespace TegmarkAux

open Matrix Polynomial TegmarkDimensionality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma charpoly_conj_diag (U : Matrix ι ι ℝ) (hU : star U * U = 1) (d : ι → ℝ) :
    (U * diagonal d * star U).charpoly = ∏ i, (X - C (d i)) := by
  rw [charpoly_mul_comm, ← mul_assoc, hU, one_mul, charpoly_diagonal]

lemma roots_conj_diag (U : Matrix ι ι ℝ) (hU : star U * U = 1) (d : ι → ℝ) :
    (U * diagonal d * star U).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [charpoly_conj_diag U hU d, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

lemma numPos_conj_diag (U : Matrix ι ι ℝ) (hU : star U * U = 1) (d : ι → ℝ) :
    numPosEigenvalues (U * diagonal d * star U) =
      (Finset.univ.filter (fun i => 0 < d i)).card := by
  unfold numPosEigenvalues
  rw [roots_conj_diag U hU d, Multiset.filter_map, Multiset.card_map]
  rfl

lemma numNeg_conj_diag (U : Matrix ι ι ℝ) (hU : star U * U = 1) (d : ι → ℝ) :
    numNegEigenvalues (U * diagonal d * star U) =
      (Finset.univ.filter (fun i => d i < 0)).card := by
  unfold numNegEigenvalues
  rw [roots_conj_diag U hU d, Multiset.filter_map, Multiset.card_map]
  rfl

lemma main (g : Matrix ι ι ℝ) (hg : g.IsSymm)
    (hsum : numPosEigenvalues g + numNegEigenvalues g = Fintype.card ι) :
    g⁻¹.IsSymm ∧ numPosEigenvalues g⁻¹ = numPosEigenvalues g ∧
      numNegEigenvalues g⁻¹ = numNegEigenvalues g := by
  have hH : g.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hg
  set U : Matrix ι ι ℝ := (hH.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  set d : ι → ℝ := hH.eigenvalues with hd
  have hU1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hgeq : g = U * diagonal d * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, d]
  have hpos := numPos_conj_diag U hU1 d
  have hneg := numNeg_conj_diag U hU1 d
  rw [← hgeq] at hpos hneg
  -- no zero eigenvalue
  have hnz : ∀ i, d i ≠ 0 := by
    intro i hi
    have hdisj : Disjoint (Finset.univ.filter (fun i => 0 < d i))
        (Finset.univ.filter (fun i => d i < 0)) := by
      rw [Finset.disjoint_filter]
      intro x _ h1 h2
      linarith
    have hsub : (Finset.univ.filter (fun i => 0 < d i)) ∪
        (Finset.univ.filter (fun i => d i < 0)) ⊆ Finset.univ.erase i := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      rcases hx with hx | hx <;> linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ _),
      ← hpos, ← hneg, hsum, Finset.card_univ] at this
    have hpos' : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  have hinv : g⁻¹ = U * diagonal (fun i => (d i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hgeq]
    have : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      exact mul_inv_cancel₀ (hnz i)
    calc U * diagonal d * star U * (U * diagonal (fun i => (d i)⁻¹) * star U)
        = U * (diagonal d * (star U * U) * diagonal (fun i => (d i)⁻¹)) * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, this, Matrix.mul_one, hU2]
  refine ⟨hg.inv, ?_, ?_⟩
  · rw [hinv, numPos_conj_diag U hU1, hpos]
    congr 1
    ext i
    simp [inv_pos]
  · rw [hinv, numNeg_conj_diag U hU1, hneg]
    congr 1
    ext i
    simp

end TegmarkAux

open TegmarkDimensionality in
theorem solution (n m : ℕ)
    (g : Matrix (Fin (n + m)) (Fin (n + m)) ℝ) (hg : g.IsSymm)
    (hpos : numPosEigenvalues g = m) (hneg : numNegEigenvalues g = n) :
    (IsElliptic g⁻¹ ↔ (n = 0 ∨ m = 0)) ∧
      (IsHyperbolic g⁻¹ ↔ (n = 1 ∨ m = 1)) ∧
      (IsUltrahyperbolic g⁻¹ ↔ (2 ≤ n ∧ 2 ≤ m)) := by
  obtain ⟨hs, hp, hn⟩ := TegmarkAux.main g hg (by rw [hpos, hneg, Fintype.card_fin]; omega)
  rw [hpos] at hp
  rw [hneg] at hn
  unfold IsElliptic IsHyperbolic IsUltrahyperbolic
  rw [hp, hn, Fintype.card_fin]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨_, h⟩; omega
    · intro h; exact ⟨hs, by omega⟩
  · constructor
    · rintro ⟨_, h⟩; omega
    · intro h; exact ⟨hs, by omega⟩
  · constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨hs, h2, h1⟩
