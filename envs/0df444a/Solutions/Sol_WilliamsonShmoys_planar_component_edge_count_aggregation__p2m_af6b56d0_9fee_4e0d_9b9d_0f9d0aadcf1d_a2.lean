-- Prove2me | solution 1 for WilliamsonShmoys.planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:53.743011+00:00
-- url     : https://prove2.me/submissions/fdd4e830-65ae-48e2-96d9-cb5e9cc9c644

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
import Theorems.Thm_WilliamsonShmoys_planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
import Theorems.Thm_WilliamsonShmoys_component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hadj : ∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C)
    (hconn : ∀ C, C ∈ parts → (M.induce (C : Set V)).Connected)
    (hdraw : ∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V)))
    (hlarge : ∀ C, C ∈ parts →
      3 ≤ Fintype.card {x : V // x ∈ C} →
      (M.induce (C : Set V)).edgeSet.ncard + 6 ≤
        3 * Fintype.card {x : V // x ∈ C})
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hlocal :
      ∀ C, C ∈ parts →
        (M.induce (C : Set V)).edgeSet.ncard +
          (if 3 ≤ Fintype.card {x : V // x ∈ C} then 6
           else if Fintype.card {x : V // x ∈ C} = 2 then 5 else 3)
          ≤ 3 * Fintype.card {x : V // x ∈ C} :=
    WilliamsonShmoys.planar_component_local_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
      M parts hnonempty hconn hdraw hlarge
  have hagg :
      M.edgeSet.ncard ≤
        ∑ C ∈ parts, (M.induce (C : Set V)).edgeSet.ncard :=
    WilliamsonShmoys.planar_component_edge_aggregation__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
      M parts hcover hdisjoint hadj
  exact WilliamsonShmoys.component_bounds_imply_global_planar_edge_bound__p2m_98235c6f_660a_40d6_a6c4_218b22f2584f_a1
    M parts hcover hnonempty hdisjoint hcard hlocal hagg