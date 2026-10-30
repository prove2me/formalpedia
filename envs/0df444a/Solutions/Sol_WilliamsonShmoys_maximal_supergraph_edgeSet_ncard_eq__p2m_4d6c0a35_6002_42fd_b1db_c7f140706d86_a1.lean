-- Prove2me | solution 1 for WilliamsonShmoys.maximal_supergraph_edgeSet_ncard_eq__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:31.207646+00:00
-- url     : https://prove2.me/submissions/2d92c567-7157-43d9-b25f-acada4bbf77b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L M : SimpleGraph V)
    (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ L)
    (hLM : L ≤ M)
    (hMDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    L.edgeSet.ncard = M.edgeSet.ncard := by
  have hML : M ≤ L := hMax M hLM hMDraw
  have hEq : L = M := le_antisymm hLM hML
  rw [hEq]