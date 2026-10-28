-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:56:03.723197+00:00
-- url     : https://prove2.me/submissions/5ae5a40f-9700-4666-b7f0-964ccd24dd0c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  classical
  have hfin : ({J : SimpleGraph V | G ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J}).Finite :=
    Set.toFinite _
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image _ (fun J : SimpleGraph V => J.edgeSet.ncard) hfin
    ⟨G, le_rfl, hG⟩
  refine ⟨H, fun u v h => hH.1 h, hmax G ⟨le_rfl, hG⟩, hH.2, fun K hK hPK => ?_⟩
  exact hmax K ⟨le_trans hH.1 (fun u v h => hK h), hPK⟩
