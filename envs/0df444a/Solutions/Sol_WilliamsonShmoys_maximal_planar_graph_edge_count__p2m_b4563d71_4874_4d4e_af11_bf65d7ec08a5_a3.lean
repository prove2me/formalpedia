-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:54:30.721106+00:00
-- url     : https://prove2.me/submissions/b3619e0e-1c61-4177-817c-64b2c2b7c384

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨M, hMplanar, hLM, hMcount⟩ :=
    WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_2a4e0817_5ede_4993_80da_c0938cce21b3_a1
      L hplanar hcard
  have hML : M = L := hmax M hMplanar hLM
  rw [hML] at hMcount
  exact hMcount