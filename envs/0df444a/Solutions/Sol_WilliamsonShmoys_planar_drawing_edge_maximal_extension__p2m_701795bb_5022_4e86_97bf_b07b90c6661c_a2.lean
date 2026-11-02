-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_extension__p2m_701795bb_5022_4e86_97bf_b07b90c6661c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:57.132832+00:00
-- url     : https://prove2.me/submissions/fbff0daf-3e03-43f5-8b2c-c343a0f68665

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    [DecidableRel P.Adj] :
    ∃ H : SimpleGraph V,
      P ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) ∧
      (∀ [DecidableRel H.Adj], P.edgeFinset.card ≤ H.edgeFinset.card) := by
  obtain ⟨H, hPH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_planar_edge_maximal_supergraph__p2m_65bb11c9_29c3_416d_befd_00639d3c1860_a1
      P hP
  refine ⟨H, hPH, hH, hmax, ?_⟩
  intro _
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hPH)