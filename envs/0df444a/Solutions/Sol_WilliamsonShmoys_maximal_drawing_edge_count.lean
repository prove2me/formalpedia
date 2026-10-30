-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawing_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:12:39.672047+00:00
-- url     : https://prove2.me/submissions/16eb1eaf-ffb1-43f7-a52a-d52e24c78844

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planarDrawingOn_triangulation_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn G → G = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨G, hsub, hG, hcount⟩ :=
    WilliamsonShmoys.planarDrawingOn_triangulation_extension H hH hV
  have hGH : G = H := hmax G hsub hG
  rw [hGH] at hcount
  exact hcount