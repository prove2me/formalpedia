-- Prove2me | solution 1 for WilliamsonShmoys.sum_component_edge_bound_from_unit__p2m_da5c5f9f_f118_4e97_97ba_a26f16bf9a38_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:25:46.397745+00:00
-- url     : https://prove2.me/submissions/5154cfed-5f60-42d8-81bf-9ffa4bba07e2

import Mathlib

set_option autoImplicit false

theorem solution {ι : Type} (parts : Finset ι) (c e : ι → Nat)
    (htotal : 3 ≤ ∑ i ∈ parts, c i)
    (hpoint : ∀ i ∈ parts, e i ≤ c i) :
    (∑ i ∈ parts, e i) + 6 ≤ 3 * (∑ i ∈ parts, c i) := by
  have hsum : (∑ i ∈ parts, e i) ≤ ∑ i ∈ parts, c i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hpoint i hi
  omega