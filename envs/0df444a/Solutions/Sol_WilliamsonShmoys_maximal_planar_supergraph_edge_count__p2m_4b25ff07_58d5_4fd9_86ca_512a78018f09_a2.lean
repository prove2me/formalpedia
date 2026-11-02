-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:26:14.263202+00:00
-- url     : https://prove2.me/submissions/388e7090-a333-42da-ae2e-23740f550784
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hmax :
      (letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
       K.edgeFinset ⊆ L.edgeFinset ∧
       HasPlanarDrawingOn L ∧
       ∀ M : SimpleGraph V,
         L.edgeFinset ⊆ M.edgeFinset →
         HasPlanarDrawingOn M →
         M.edgeFinset = L.edgeFinset)) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
    fun G => Classical.decRel G.Adj
  have hlower :=
    WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
      K L hcard hmax
  rcases hmax with ⟨hsub, hdraw, hmaximal⟩
  have hupper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
      L hcard hdraw
  omega