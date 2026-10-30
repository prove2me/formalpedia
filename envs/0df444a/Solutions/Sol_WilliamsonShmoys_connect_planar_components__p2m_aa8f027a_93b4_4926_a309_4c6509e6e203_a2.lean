-- Prove2me | solution 1 for WilliamsonShmoys.connect_planar_components__p2m_aa8f027a_93b4_4926_a309_4c6509e6e203_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:59.963794+00:00
-- url     : https://prove2.me/submissions/c7ddec23-4725-4414-82cc-42a364a9fa21
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, L.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hsub, hconn, hHdraw⟩ :=
    WilliamsonShmoys.connect_planar_supergraph_extension__p2m_70db2af0_0d6e_4990_9f4e_a19bbb8e6b51_a1
      L hDraw hV
  exact ⟨H, Set.ncard_le_ncard hsub, hconn, hHdraw⟩