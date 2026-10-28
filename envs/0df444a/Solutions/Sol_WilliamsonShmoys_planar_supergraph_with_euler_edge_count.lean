-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_with_euler_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:25:38.056988+00:00
-- url     : https://prove2.me/submissions/21df1e75-bd69-4494-b34b-6731b4215cc8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5

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
  obtain ⟨L, hL, hKL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal K hK hV
  have hedge :=
    WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5
      L hL hV hmax
  exact ⟨L, hL, hKL, hedge⟩