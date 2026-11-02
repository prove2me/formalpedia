-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_e3fcbf10_6f41_4741_b7a4_cf721019c4f7_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:45:31.851346+00:00
-- url     : https://prove2.me/submissions/10c168cc-a5f8-4bde-ae9b-a0e2ae7ab79e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        (letI : DecidableRel U.Adj := Classical.decRel U.Adj
         U.edgeFinset.card = 3 * Fintype.card V - 6) := by
  obtain ⟨U, hTU, hU, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1 T hT
  refine ⟨U, hTU, hU, ?_⟩
  letI : DecidableRel U.Adj := Classical.decRel U.Adj
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_dcc51884_0da8_465d_ba77_04c61fbeb5d3_a1 U hV hU hmax