-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_bc188a74_c743_4521_84db_ff6e1b478f87_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:39:22.10596+00:00
-- url     : https://prove2.me/submissions/5e12fc29-bc11-4e6c-8aef-3ced01e59f79

import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : HasPlanarDrawingOn R)
    (hcard : 3 ≤ Fintype.card V) :
    ∀ [hRdec : DecidableRel R.Adj],
      R.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  classical
  intro hRdec
  obtain ⟨S, hsub, _hSdraw, hScard⟩ :=
    WilliamsonShmoys.planar_triangulation_extension__p2m_aa8c3543_6a70_4578_ab0d_df04a85e5168_a1
      R hR hcard
  calc
    R.edgeFinset.card ≤ S.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hsub)
    _ = 3 * Fintype.card V - 6 := hScard