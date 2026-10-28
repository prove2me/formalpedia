-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_has_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:12:53.352376+00:00
-- url     : https://prove2.me/submissions/f804d8fb-04fb-4f17-9a18-3fd4b0341a3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_has_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (K : SimpleGraph V)
    (hNK : N ≤ K)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, N ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply WilliamsonShmoys.maximal_planar_drawingOn_has_triangulation_edge_count
      K hK hV
  intro L hKL hL
  exact hmax L (le_trans hNK hKL) hL