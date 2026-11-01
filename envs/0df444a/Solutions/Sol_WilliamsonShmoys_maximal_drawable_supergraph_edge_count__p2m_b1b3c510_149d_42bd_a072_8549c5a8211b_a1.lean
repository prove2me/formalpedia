-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_supergraph_edge_count__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:18:06.817959+00:00
-- url     : https://prove2.me/submissions/f96bfde9-f610-49fc-ae8b-fd868a8cafff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  have hupper := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
    L hL hcard
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_055d45fa_a44d_4012_991d_80fcbbc5becb_a1
    L hL hmax hcard
  omega