-- Prove2me | solution 1 for WilliamsonShmoys.component_planar_edge_bound_from_drawing__p2m_dad39d86_4ed1_4b9b_930d_705a080f17ad_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T07:03:02.830997+00:00
-- url     : https://prove2.me/submissions/c423d118-7ec1-4e63-8d20-e43c5e6148eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (C : L.ConnectedComponent)
    (hcard : 3 <= C.supp.ncard) :
    C.toSimpleGraph.edgeSet.ncard + 6 <= 3 * C.supp.ncard := by
  letI : Fintype C.supp := Fintype.ofFinite C.supp
  obtain ⟨M, hCount, hDraw, hMax⟩ :=
    WilliamsonShmoys.component_maximal_planar_extension__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
      L hL C
  obtain ⟨f, hEuler, hTriangle⟩ :=
    WilliamsonShmoys.maximal_planar_face_euler_equations__p2m_de0e1a5b_8d3a_47e8_9bfe_9457c1edc302_a1
      L C M hDraw hMax hcard
  omega
