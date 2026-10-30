-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bound_from_witness__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:19.487421+00:00
-- url     : https://prove2.me/submissions/5fc5e1f7-6030-4504-ac91-88a645af4391

import Mathlib

set_option autoImplicit false

theorem solution
    {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (hpoint : ∀ i ∈ parts, e i ≤ 3 * c i)
    (hwitness : ∃ i ∈ parts, e i + 6 ≤ 3 * c i) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by
  classical
  rcases hwitness with ⟨i, hi, hslack⟩
  have hrest : (∑ j ∈ parts.erase i, e j) ≤
      (∑ j ∈ parts.erase i, 3 * c j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint j (Finset.mem_of_mem_erase hj)
  have hrest' : (∑ j ∈ parts.erase i, e j) ≤
      3 * (∑ j ∈ parts.erase i, c j) := by
    simpa [Finset.mul_sum] using hrest
  have he : (∑ j ∈ parts, e j) =
      (∑ j ∈ parts.erase i, e j) + e i := by
    simpa using (Finset.sum_erase_add (s := parts) (f := e) (a := i) hi).symm
  have hc : (∑ j ∈ parts, c j) =
      (∑ j ∈ parts.erase i, c j) + c i := by
    simpa using (Finset.sum_erase_add (s := parts) (f := c) (a := i) hi).symm
  rw [he, hc]
  omega