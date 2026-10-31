-- Prove2me | solution 2 for WilliamsonShmoys.planar_completion_edge_bound__p2m_6d23e6d9_3a8b_46d0_86a1_79ef2bae4d90_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:35:43.756065+00:00
-- url     : https://prove2.me/submissions/39e827ab-a5a5-43fe-871c-b5154302ee38

import Theorems.Thm_WilliamsonShmoys_planar_drawing_dense_supergraph

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      3 * Fintype.card V - 6 ≤ Q.edgeSet.ncard :=
  WilliamsonShmoys.planar_drawing_dense_supergraph P hCard hP
