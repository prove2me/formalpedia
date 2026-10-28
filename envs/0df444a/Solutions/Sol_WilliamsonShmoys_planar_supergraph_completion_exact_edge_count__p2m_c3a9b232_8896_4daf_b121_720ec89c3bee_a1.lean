-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_completion_exact_edge_count__p2m_c3a9b232_8896_4daf_b121_720ec89c3bee_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:35:05.010229+00:00
-- url     : https://prove2.me/submissions/9d3bcd9a-ba41-4fd4-b81a-e4f050752049
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H)
          (H.edgeSet.ncard = 3 * Fintype.card V - 6))) := by
  cases WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2 G hG with
  | intro H h =>
    cases h with
    | intro hGH h =>
      cases h with
      | intro hH hmax =>
        have hcount :=
          WilliamsonShmoys.maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
            H hH hV hmax
        exact Exists.intro H (And.intro hGH (And.intro hH hcount))