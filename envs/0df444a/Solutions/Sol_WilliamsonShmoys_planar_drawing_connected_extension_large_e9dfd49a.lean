-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_large_e9dfd49a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T05:03:15.911546+00:00
-- url     : https://prove2.me/submissions/c5079c65-b8c4-4d85-8f59-0667754597a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by
  obtain ⟨H, hGH, hHdraw, hHconn⟩ :=
    WilliamsonShmoys.planar_drawing_connected_supergraph_large_9dbc1b44_5e81_4cbc_9338_84418c6013a1
      G hG hCard
  exact ⟨H, hGH, hHdraw, hHconn,
    WilliamsonShmoys.edgeSet_ncard_mono_9dbc1b44_5e81_4cbc_9338_84418c6013a1 G H hGH⟩