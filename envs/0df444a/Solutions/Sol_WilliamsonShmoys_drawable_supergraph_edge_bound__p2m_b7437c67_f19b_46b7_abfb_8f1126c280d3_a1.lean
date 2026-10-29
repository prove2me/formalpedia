-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_edge_bound__p2m_b7437c67_f19b_46b7_abfb_8f1126c280d3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:23:42.584669+00:00
-- url     : https://prove2.me/submissions/70151e9d-2431-4685-b780-dbb344f66c50
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨L, hKL, hLDraw, f, hEuler, hIncidence⟩ :=
    WilliamsonShmoys.drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2
      K hDraw hCard
  refine ⟨L, hKL, hLDraw, ?_⟩
  omega