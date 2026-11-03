-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:14:12.698191+00:00
-- url     : https://prove2.me/submissions/8f3a3ab2-035a-41a7-a102-97252901b14f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
     3 * Fintype.card V - 6 ≤ L.edgeFinset.card) := by
  apply WilliamsonShmoys.maximal_drawable_supergraph_edge_bound__p2m_16f13def_1905_44d4_887c_a7f874e9f4a3_a3 L hV hL
  intro M hsub hdraw u v huv
  exact hmax M hsub hdraw huv
