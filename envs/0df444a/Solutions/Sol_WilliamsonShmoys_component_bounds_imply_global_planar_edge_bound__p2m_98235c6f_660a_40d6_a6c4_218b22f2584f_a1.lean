-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:04.919548+00:00
-- url     : https://prove2.me/submissions/cc02f5e7-e9d9-44af-96fa-59eefd32c087

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
import Theorems.Thm_WilliamsonShmoys_partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
import Theorems.Thm_WilliamsonShmoys_partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hcard : 3 ≤ Fintype.card V)
    (hlocal : ∀ C, C ∈ parts →
      (M.induce (C : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
         else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)
        ≤ 3 * Fintype.card {x : V // x ∈ C})
    (hagg : M.edgeSet.ncard ≤
      ∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  calc
    M.edgeSet.ncard + 6 ≤
        (∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard) +
          (∑ C ∈ parts,
            (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
             else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)) := by
      have hdef :=
        WilliamsonShmoys.partition_deficit_sum_lower_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
          (V := V) parts hcover hnonempty hdisjoint hcard
      omega
    _ = ∑ C ∈ parts,
        ((M.induce (C : Set V)).edgeSet.ncard +
          (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
           else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ 3 * ∑ C ∈ parts, Fintype.card {x : V // x ∈ C} :=
      WilliamsonShmoys.component_local_sum_bound__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
        (V := V) M parts hlocal
    _ = 3 * Fintype.card V := by
      rw [WilliamsonShmoys.partition_cardinality_sum__p2m_2f886b64_45e5_4692_a31b_5084b02f539f_a1
        (V := V) parts hcover hdisjoint]
