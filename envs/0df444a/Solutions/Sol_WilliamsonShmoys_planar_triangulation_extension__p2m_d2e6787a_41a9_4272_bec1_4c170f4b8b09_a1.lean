-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_d2e6787a_41a9_4272_bec1_4c170f4b8b09_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:57:43.658936+00:00
-- url     : https://prove2.me/submissions/bf2081d9-f64a-479c-939e-1c1248f89993

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ S : SimpleGraph V, R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
      (letI : DecidableRel S.Adj := Classical.decRel S.Adj
       S.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨S, hRS, hS, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
      R hR hcard
  refine ⟨S, hRS, hS, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_f8b110d8_67db_4582_b9bf_9e52697d207d_a1
    S hS hcard hmax