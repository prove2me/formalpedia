-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_extension_of_planar_drawing__p2m_feadab3c_5ccb_4a82_9ee7_4f0db9bfa441_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:33:24.694733+00:00
-- url     : https://prove2.me/submissions/659c9152-425b-4328-aa23-8be5c4e959d7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U)
    (hconn : U.Connected) :
    ∃ T : SimpleGraph V, U ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨T, hUT, hT, hconnT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
      U hV hU hconn
  refine ⟨T, hUT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
    T hV hconnT hT hmax