-- Prove2me | solution 1 for WilliamsonShmoys.drawable_supergraph_face_count__p2m_b2793381_3dc8_4ae5_ab06_93034309e127_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T22:57:27.467729+00:00
-- url     : https://prove2.me/submissions/e0521f5d-3804-4c90-b4f0-c10527734504
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_count__p2m_37df6a54_88e4_4a1c_bff9_1bc979b9e8cf_a3

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∃ f : ℕ,
        Fintype.card V + f = L.edgeSet.ncard + 2 ∧
        3 * f = 2 * L.edgeSet.ncard := by
  classical
  obtain ⟨L, hKL, hDrawL, hEdges⟩ :=
    WilliamsonShmoys.drawable_supergraph_edge_count__p2m_37df6a54_88e4_4a1c_bff9_1bc979b9e8cf_a3
      K hDraw hCard
  refine ⟨L, hKL, hDrawL, 2 * Fintype.card V - 4, ?_, ?_⟩
  · rw [hEdges]
    omega
  · rw [hEdges]
    omega