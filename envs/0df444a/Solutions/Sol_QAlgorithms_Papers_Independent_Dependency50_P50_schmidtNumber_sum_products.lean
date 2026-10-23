-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P50.schmidtNumber_sum_products
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:59:46.466177+00:00
-- url     : https://prove2.me/submissions/c420ab0f-395c-4a36-b8e1-337e267bde69

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P50
noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P50 in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (s : ℕ) (x : Fin s → EuclideanSpace ℂ (Fin n)) (y : Fin s → EuclideanSpace ℂ (Fin m)) :
    schmidtNumber (∑ i : Fin s, QAlgorithms.tensorVec (x i) (y i)) ≤ s := by
  unfold schmidtNumber
  have hfac : (Matrix.of fun (i : Fin n) (j : Fin m) =>
      (∑ k : Fin s, QAlgorithms.tensorVec (x k) (y k)) (i, j)) =
      (Matrix.of fun (i : Fin n) (k : Fin s) => x k i) *
        (Matrix.of fun (k : Fin s) (j : Fin m) => y k j) := by
    ext i j
    simp [Matrix.mul_apply, QAlgorithms.tensorVec, WithLp.ofLp_sum]
  rw [hfac]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  simpa using Matrix.rank_le_card_width (Matrix.of fun (i : Fin n) (k : Fin s) => x k i)
