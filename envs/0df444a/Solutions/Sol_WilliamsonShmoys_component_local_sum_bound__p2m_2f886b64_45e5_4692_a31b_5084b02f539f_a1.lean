-- Prove2me | solution 1 for WilliamsonShmoys.component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:22.606194+00:00
-- url     : https://prove2.me/submissions/8c4b447d-7d56-46f6-be26-7cd7e3e14957

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (M : SimpleGraph V) (parts : Finset (Finset V))
    (hlocal : ∀ C, C ∈ parts →
      (M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3) ≤
      3 * Fintype.card {x : V // x ∈ C}) :
    (∑ C ∈ parts,
      ((M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3))) ≤
      3 * ∑ C ∈ parts, Fintype.card {x : V // x ∈ C} := by
  calc
    _ ≤ ∑ C ∈ parts, 3 * Fintype.card {x : V // x ∈ C} := by
      apply Finset.sum_le_sum
      intro C hC
      exact hlocal C hC
    _ = 3 * ∑ C ∈ parts, Fintype.card {x : V // x ∈ C} := by
      rw [Finset.mul_sum]