-- Prove2me | solution 1 for TegmarkDimensionality.signature_examples
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:55:58.516982+00:00
-- url     : https://prove2.me/submissions/25239484-8a32-4d23-b0de-5f55be3cba87

import Mathlib
import Definitions.Def_tegmark_pde_classification
import Theorems.Thm_TegmarkDimensionality_field_equation_type_by_signature

open TegmarkDimensionality Matrix Finset Polynomial

namespace TegmarkSignatureExamples

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma roots_diagonal (d : ι → ℝ) :
    (diagonal d).charpoly.roots = Multiset.map d Finset.univ.val := by
  rw [charpoly_diagonal, roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, X_sub_C_ne_zero]

lemma numPos_diagonal (d : ι → ℝ) :
    numPosEigenvalues (diagonal d) = (univ.filter (fun i => 0 < d i)).card := by
  unfold numPosEigenvalues
  rw [roots_diagonal d, Multiset.filter_map, Multiset.card_map]
  rfl

lemma numNeg_diagonal (d : ι → ℝ) :
    numNegEigenvalues (diagonal d) = (univ.filter (fun i => d i < 0)).card := by
  unfold numNegEigenvalues
  rw [roots_diagonal d, Multiset.filter_map, Multiset.card_map]
  rfl

end TegmarkSignatureExamples

open TegmarkSignatureExamples in
theorem solution :
    IsHyperbolic (Matrix.diagonal (![1, -1, -1, -1] : Fin 4 → ℝ))⁻¹ ∧
      IsElliptic (Matrix.diagonal (![1, 1, 1, 1, 1] : Fin 5 → ℝ))⁻¹ ∧
      IsUltrahyperbolic (Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℝ))⁻¹ := by
  refine ⟨?_, ?_, ?_⟩
  · -- hyperbolic (+---)
    set g : Matrix (Fin 4) (Fin 4) ℝ := diagonal (![1, -1, -1, -1])
    have hg : g.IsSymm := by simp [g, Matrix.isSymm_diagonal]
    have hpos : numPosEigenvalues g = 1 := by
      rw [show g = diagonal _ from rfl, numPos_diagonal]
      have : univ.filter (fun i : Fin 4 => 0 < (![1, -1, -1, -1] : Fin 4 → ℝ) i) = {0} := by
        ext i; fin_cases i <;> simp
      rw [this, Finset.card_singleton]
    have hneg : numNegEigenvalues g = 3 := by
      rw [show g = diagonal _ from rfl, numNeg_diagonal]
      have : univ.filter (fun i : Fin 4 => (![1, -1, -1, -1] : Fin 4 → ℝ) i < 0) = {1, 2, 3} := by
        ext i; fin_cases i <;> simp
      rw [this]
      simp
    have h := (field_equation_type_by_signature 3 1 g hg hpos hneg).2.1
    exact h.2 (Or.inr rfl)
  · -- elliptic (+++++)
    set g : Matrix (Fin 5) (Fin 5) ℝ := diagonal (![1, 1, 1, 1, 1])
    have hg : g.IsSymm := by simp [g, Matrix.isSymm_diagonal]
    have hpos : numPosEigenvalues g = 5 := by
      rw [show g = diagonal _ from rfl, numPos_diagonal]
      have : univ.filter (fun i : Fin 5 => 0 < (![1, 1, 1, 1, 1] : Fin 5 → ℝ) i) = univ := by
        ext i; fin_cases i <;> simp
      rw [this, Finset.card_univ, Fintype.card_fin]
    have hneg : numNegEigenvalues g = 0 := by
      rw [show g = diagonal _ from rfl, numNeg_diagonal]
      have : univ.filter (fun i : Fin 5 => (![1, 1, 1, 1, 1] : Fin 5 → ℝ) i < 0) = ∅ := by
        ext i; fin_cases i <;> simp
      rw [this, Finset.card_empty]
    have h := (field_equation_type_by_signature 0 5 g hg hpos hneg).1
    exact h.2 (Or.inl rfl)
  · -- ultrahyperbolic (++--)
    set g : Matrix (Fin 4) (Fin 4) ℝ := diagonal (![1, 1, -1, -1])
    have hg : g.IsSymm := by simp [g, Matrix.isSymm_diagonal]
    have hpos : numPosEigenvalues g = 2 := by
      rw [show g = diagonal _ from rfl, numPos_diagonal]
      have : univ.filter (fun i : Fin 4 => 0 < (![1, 1, -1, -1] : Fin 4 → ℝ) i) = {0, 1} := by
        ext i; fin_cases i <;> simp
      rw [this, Finset.card_pair (by decide)]
    have hneg : numNegEigenvalues g = 2 := by
      rw [show g = diagonal _ from rfl, numNeg_diagonal]
      have : univ.filter (fun i : Fin 4 => (![1, 1, -1, -1] : Fin 4 → ℝ) i < 0) = {2, 3} := by
        ext i; fin_cases i <;> simp
      rw [this, Finset.card_pair (by decide)]
    have h := (field_equation_type_by_signature 2 2 g hg hpos hneg).2.2
    exact h.2 ⟨le_rfl, le_rfl⟩
