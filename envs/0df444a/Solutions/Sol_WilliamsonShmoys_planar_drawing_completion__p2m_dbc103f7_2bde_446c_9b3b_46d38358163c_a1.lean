-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_completion__p2m_dbc103f7_2bde_446c_9b3b_46d38358163c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:25:28.011277+00:00
-- url     : https://prove2.me/submissions/102c86db-1838-4590-a7d3-3f7383b0ca88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ K : SimpleGraph V,
      letI : DecidableRel K.Adj := Classical.decRel K.Adj
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  classical
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  obtain ⟨K, hHK, hK, hCard, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
      H hV hH
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  have hEuler :=
    WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_28ba4808_169d_4087_9472_de8f0bf86338_a1
      K hV hK hMax
  exact ⟨K, hHK, hK, hCard, hEuler⟩