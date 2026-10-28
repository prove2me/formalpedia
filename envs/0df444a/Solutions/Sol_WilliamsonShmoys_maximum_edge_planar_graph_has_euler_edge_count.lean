-- Prove2me | solution 1 for WilliamsonShmoys.maximum_edge_planar_graph_has_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:35:33.537333+00:00
-- url     : https://prove2.me/submissions/94288a6b-5df1-44a9-9190-17a7617b5da0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_f686dd19
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_f686dd19

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_edge_count_le_f686dd19 N hV hN
  obtain ⟨K, hNK, hKdraw, hKcount⟩ :=
    WilliamsonShmoys.planar_supergraph_triangulation_f686dd19 N hV hN
  have hmaxK := hmax K hNK hKdraw
  have hlower : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by
    calc
      3 * Fintype.card V = K.edgeSet.ncard + 6 := hKcount.symm
      _ ≤ N.edgeSet.ncard + 6 := Nat.add_le_add_right hmaxK 6
  exact Nat.le_antisymm hlower hupper