-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_edge_card
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:32:48.100029+00:00
-- url     : https://prove2.me/submissions/ae18b855-4930-48a6-bc28-7e2869261cb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
import Theorems.Thm_WilliamsonShmoys_edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 <= Fintype.card V)
    (hConnected : S.Connected) :
    exists T : SimpleGraph V,
      (forall u v, S.Adj u v -> T.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn T /\
      S.edgeSet.ncard <= T.edgeSet.ncard /\
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hST, hTPlanar, hSTCard, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3 S hS
  refine ⟨T, hST, hTPlanar, hSTCard, ?_⟩
  exact WilliamsonShmoys.edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3 T hCard hTPlanar hMax