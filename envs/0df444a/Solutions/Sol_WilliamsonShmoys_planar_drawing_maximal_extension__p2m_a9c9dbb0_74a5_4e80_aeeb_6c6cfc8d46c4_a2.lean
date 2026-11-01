-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:48:19.781649+00:00
-- url     : https://prove2.me/submissions/71715365-ebc6-4c88-a9fd-fb6fc305a1a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
       (letI : DecidableRel H.Adj := Classical.decRel H.Adj
        L.edgeFinset.card ≤ H.edgeFinset.card)) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_has_maximal_extension__p2m_c3b679a7_5abb_4fff_8dba_61888269c901_a1 L hL
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, hLH, hH, hmax, ?_⟩
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hLH)