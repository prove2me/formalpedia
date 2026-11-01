-- Prove2me | solution 1 for WilliamsonShmoys.inclusion_maximal_planar_graph_edge_count__p2m_d9484fdc_deb9_4095_abe2_5d54d805080e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:31:12.722745+00:00
-- url     : https://prove2.me/submissions/2af4ac5c-6d07-4584-9e27-2162e57a2a60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
      H hH
  have hKH : K = H := hmax K hHK hK
  have hcount :=
    WilliamsonShmoys.maximal_drawable_edge_count__p2m_e6f2f448_1eb8_42c3_a63b_d113f4e2074c_a3
      K hcard hK hKmax
  cases hKH
  exact hcount