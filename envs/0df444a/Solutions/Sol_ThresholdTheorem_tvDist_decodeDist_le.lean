-- Prove2me | solution 1 for ThresholdTheorem.tvDist_decodeDist_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T01:46:39.325816+00:00
-- url     : https://prove2.me/submissions/36919fcb-c53a-42e0-97d3-1e5119bf77ab

import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

theorem solution {n b : ℕ}
    (dec : (Fin b → Fin 2) → Fin 2)
    (P Q : (Fin n × Fin b → Fin 2) → ℝ) :
    tvDist (decodeDist dec P) (decodeDist dec Q) ≤ tvDist P Q := by
  classical
  unfold tvDist decodeDist
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  set f : (Fin n × Fin b → Fin 2) → (Fin n → Fin 2) := fun x i => dec (fun j => x (i, j)) with hf
  calc ∑ y, |∑ x ∈ Finset.univ.filter (fun x => (fun i => dec (fun j => x (i, j))) = y), P x -
          ∑ x ∈ Finset.univ.filter (fun x => (fun i => dec (fun j => x (i, j))) = y), Q x|
      ≤ ∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), |P x - Q x| := by
        apply Finset.sum_le_sum
        intro y _
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |P x - Q x| := Finset.sum_fiberwise _ _ _
