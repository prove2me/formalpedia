-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono__p2m_f10915d7_3b63_441c_afee_bba7154a1b1e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:02.978463+00:00
-- url     : https://prove2.me/submissions/1f823e5b-85c9-4ee8-91d4-86f9b4901372

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V)
    (hEdges : L.edgeSet ⊆ H.edgeSet) : L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard hEdges