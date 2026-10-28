-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T11:43:40.999995+00:00
-- url     : https://prove2.me/submissions/fd4c061b-ac69-4706-84ae-eefbffc44fd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_adj_inclusion

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      H.Connected ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hsub, hconn, hdraw⟩ :=
    WilliamsonShmoys.planarDrawing_connected_supergraph G hGdraw hCard
  exact ⟨H, hsub, hconn, hdraw,
    WilliamsonShmoys.edgeSet_ncard_mono_of_adj_inclusion G H hsub⟩