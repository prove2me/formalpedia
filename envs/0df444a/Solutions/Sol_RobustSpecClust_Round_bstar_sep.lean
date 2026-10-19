-- Prove2me | solution 1 for RobustSpecClust.Round.bstar_sep
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T10:46:42.103183+00:00
-- url     : https://prove2.me/submissions/1dbb605a-a215-4690-b185-5af3ec89b50b

import Definitions.Def_RobustSpecClust_Round_Setting

open RobustSpecClust.Round

theorem solution {n r : ℕ} (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (k l : Fin r) (hkl : k ≠ l) :
    vecNorm ((Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) l -
        (Matrix.diagonal (fun j => 1 / Real.sqrt (clusterSize φ j)) * O) k)
      = Real.sqrt (1 / (clusterSize φ k : ℝ) + 1 / (clusterSize φ l : ℝ)) := by
  -- the rows of an orthogonal matrix are orthonormal
  have hrow : ∀ a b : Fin r, ∑ j, O a j * O b j = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun ((Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp hO) a) b
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] using h
  have hd2 : ∀ j, (1 / Real.sqrt (clusterSize φ j)) ^ 2 = 1 / (clusterSize φ j : ℝ) := by
    intro j
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  unfold vecNorm
  congr 1
  simp only [Pi.sub_apply, Matrix.diagonal_mul]
  have hexp : ∀ j, (1 / Real.sqrt (clusterSize φ l) * O l j
      - 1 / Real.sqrt (clusterSize φ k) * O k j) ^ 2
      = (1 / Real.sqrt (clusterSize φ l)) ^ 2 * (O l j * O l j)
        + (1 / Real.sqrt (clusterSize φ k)) ^ 2 * (O k j * O k j)
        - 2 * (1 / Real.sqrt (clusterSize φ l) * (1 / Real.sqrt (clusterSize φ k)))
          * (O l j * O k j) := by
    intro j; ring
  simp only [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hrow,
    if_true, hd2, hkl.symm, if_false]
  ring
