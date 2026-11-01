-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_drawing_has_3n_minus_6_edges__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:20:18.915202+00:00
-- url     : https://prove2.me/submissions/c7467db1-ac49-4aa7-a349-29d95bbcd7ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
      letI : DecidableRel U.Adj := dU
      letI : DecidableRel W.Adj := dW
      HasPlanarDrawingOn W →
      U.edgeFinset ⊆ W.edgeFinset →
      W.edgeFinset = U.edgeFinset) :
    letI : DecidableRel U.Adj := dU
    U.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  letI : DecidableRel U.Adj := dU
  obtain ⟨W, dW, hW, hsub, hmaxW⟩ :=
    WilliamsonShmoys.planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
      U dU hU
  letI : DecidableRel W.Adj := dW
  have heq : W.edgeFinset = U.edgeFinset := hmax W dW hW hsub
  have hcard : W.edgeFinset.card = 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
      W dW hW hn hmaxW
  simpa [heq] using hcard
