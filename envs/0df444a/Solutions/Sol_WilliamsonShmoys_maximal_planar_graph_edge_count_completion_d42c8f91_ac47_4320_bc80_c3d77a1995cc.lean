-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T12:07:32.324042+00:00
-- url     : https://prove2.me/submissions/dbf07190-cd59-4d14-833e-d43cd9ba5361
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_edge_count_completion_64e86cee
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_supergraph_edge_count_completion_64e86cee K hV hK
  have hLK : L <= K := hmax L hKL hL
  have hEq : K = L := le_antisymm hKL hLK
  rw [hEq]
  exact hcount