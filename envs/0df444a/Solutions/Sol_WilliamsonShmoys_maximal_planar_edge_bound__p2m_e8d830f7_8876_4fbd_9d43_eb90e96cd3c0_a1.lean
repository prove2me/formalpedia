-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:34.269261+00:00
-- url     : https://prove2.me/submissions/ceeb885c-2a76-428a-85ed-005609ce26aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel _;
     3 * Fintype.card V - 6 <= H.edgeFinset.card) := by
  classical
  rcases WilliamsonShmoys.planar_triangulation_extension__p2m_33fd9cf6_5dff_42ab_8e0f_e49b055267c2_a1
      H hH hcard with ⟨K, hHK, hK, htri⟩
  have hKH : K ≤ H := hmax K hHK hK
  have hEdges : K.edgeFinset.card ≤ H.edgeFinset.card := by
    exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)
  exact htri.trans hEdges
