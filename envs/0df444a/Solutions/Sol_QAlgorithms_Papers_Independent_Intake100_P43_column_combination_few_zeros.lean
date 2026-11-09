-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.column_combination_few_zeros
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:18:45.341029+00:00
-- url     : https://prove2.me/submissions/7538f262-3085-4ed7-94a6-7295d3107177

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Intake100.P43 in
theorem solution (m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : TotallyNonsingular M)
    (cols : Fin n ↪ Fin m) (c : Fin n → ℂ) (hc : c ≠ 0) :
    (Finset.univ.filter (fun i : Fin m =>
      (∑ j : Fin n, c j * M i (cols j)) = 0)).card ≤ n - 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq (show n ≤ (Finset.univ.filter (fun i : Fin m =>
      (∑ j : Fin n, c j * M i (cols j)) = 0)).card by omega)
  let rows : Fin n ↪ Fin m := (t.orderEmbOfFin htc).toEmbedding
  have hrows : ∀ r, (∑ j : Fin n, c j * M (rows r) (cols j)) = 0 := by
    intro r
    have hmem : rows r ∈ t := Finset.orderEmbOfFin_mem t htc r
    exact (Finset.mem_filter.mp (ht hmem)).2
  have hv : (M.submatrix rows cols) *ᵥ c = 0 := by
    funext r
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    rw [← hrows r]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  exact hc (Matrix.eq_zero_of_mulVec_eq_zero (hM n rows cols) hv)
