-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:06:13.815874+00:00
-- url     : https://prove2.me/submissions/03172da1-d3f9-45d8-ac62-3e7f00437cc5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    Exists fun L : SimpleGraph V => K <= L /\ HasPlanarDrawingOn L /\
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
        L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  exact Exists.elim
    (WilliamsonShmoys.maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
      K hK)
    (fun L hL =>
      Exists.intro L
        (And.intro hL.left
          (And.intro hL.right.left
            (WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
              L hL.right.left hL.right.right hcard))))