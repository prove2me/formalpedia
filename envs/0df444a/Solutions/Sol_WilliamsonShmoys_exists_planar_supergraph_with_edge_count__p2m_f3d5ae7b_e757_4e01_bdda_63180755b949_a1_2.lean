-- Prove2me | solution 2 for WilliamsonShmoys.exists_planar_supergraph_with_edge_count__p2m_f3d5ae7b_e757_4e01_bdda_63180755b949_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:35:11.854596+00:00
-- url     : https://prove2.me/submissions/d3e86fc6-af44-41b0-b4eb-bf44567142d8

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_euler_edge_count

set_option autoImplicit false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      K.edgeSet ⊆ L.edgeSet ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  first
  | exact _root_.WilliamsonShmoys.planar_supergraph_with_euler_edge_count
  | (apply _root_.WilliamsonShmoys.planar_supergraph_with_euler_edge_count <;> assumption)
  | (intros; apply _root_.WilliamsonShmoys.planar_supergraph_with_euler_edge_count <;> assumption)
