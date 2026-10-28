-- Prove2me | solution 1 for WilliamsonShmoys.finite_partition_edge_slack
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:51:35.661671+00:00
-- url     : https://prove2.me/submissions/69e6615e-d20b-4ef4-aea1-84de1069f975

import Mathlib
theorem solution
    {ι : Type} [Fintype ι]
    (v e : ι → Nat)
    (hv : 3 ≤ ∑ i, v i)
    (hsmall : ∀ i, v i < 3 → e i ≤ v i)
    (hlarge : ∀ i, 3 ≤ v i → e i + 6 ≤ 3 * v i) :
    (∑ i, e i) + 6 ≤ 3 * (∑ i, v i) := by
  classical
  by_cases h : ∃ i, 3 ≤ v i
  · obtain ⟨i, hi⟩ := h
    have hle : ∀ j, e j ≤ 3 * v j := by
      intro j
      by_cases hj : 3 ≤ v j
      · have := hlarge j hj; omega
      · have := hsmall j (by omega); omega
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hle j)
    rw [← Finset.mul_sum] at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have := hlarge i hi
    nlinarith
  · push_neg at h
    have h1 : ∑ i, e i ≤ ∑ i, v i := Finset.sum_le_sum fun i _ => hsmall i (h i)
    omega
