-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1818e4a7_4acb_4ee2_9cf9_24cae947314c_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:21.049589+00:00
-- url     : https://prove2.me/submissions/90efac58-67da-4681-8f3f-4a50f3de88fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
import Theorems.Thm_WilliamsonShmoys_component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  exact WilliamsonShmoys.component_aggregation_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
    U dU hcard (by
      intro S hScard hSconn
      letI : LinearOrder {x // x ∈ S} := inferInstance
      have hcardH : 3 ≤ Fintype.card {x // x ∈ S} := by
        simpa using hScard
      have hdraw : HasPlanarDrawingOn (U.induce (↑S : Set V)) :=
        WilliamsonShmoys.planar_drawing_induced_subset__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
          U dU hU S
      have hbound :=
        WilliamsonShmoys.connected_planar_edge_bound__p2m_004e5ed5_cd67_44f8_b54c_b7b595ba6dfb_a1
          (U.induce (↑S : Set V)) (Classical.decRel _) hdraw hSconn hcardH
      have hcard_eq : Fintype.card {x // x ∈ (↑S : Set V)} = S.card := by
        simpa using (Fintype.card_coe S)
      simpa only [← hcard_eq] using hbound)