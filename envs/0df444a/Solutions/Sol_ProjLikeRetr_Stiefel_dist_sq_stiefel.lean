-- Prove2me | solution 1 for ProjLikeRetr.Stiefel.dist_sq_stiefel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:46:42.178154+00:00
-- url     : https://prove2.me/submissions/818a80de-e7ae-4a28-a420-a729194ceef2

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

open scoped Matrix Matrix.Norms.Frobenius

open ProjLikeRetr.Stiefel Matrix Matrix.Norms.Frobenius in
theorem solution {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) ℝ) (hY : Y ∈ stiefel n m) :
    ‖X - Y‖ ^ 2 = ‖X‖ ^ 2 + (m : ℝ) - 2 * (Yᵀ * X).trace := by
  have hY' : Yᵀ * Y = 1 := hY
  have key : ∀ A : Matrix (Fin n) (Fin m) ℝ, ‖A‖ ^ 2 = ∑ i, ∑ j, A i j * A i j := by
    intro A
    rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast,
      ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    norm_num
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
  have hm : (∑ i, ∑ j, Y i j * Y i j) = (m : ℝ) := by
    have := congrArg Matrix.trace hY'
    rw [Matrix.trace_one, Fintype.card_fin] at this
    rw [← this, Matrix.trace, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply]
  have ht : (Yᵀ * X).trace = ∑ i, ∑ j, Y i j * X i j := by
    rw [Matrix.trace, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply]
  rw [key, key, ht, ← hm]
  simp only [Matrix.sub_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring
