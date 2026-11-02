-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_by_edge_card__p2m_9ce78458_17c3_4c03_93dc_57f21947e1ab_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:50:24.893712+00:00
-- url     : https://prove2.me/submissions/8fca8302-b515-4b2f-af54-eca96448b7f6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        Set.ncard H.edgeSet ≥ Set.ncard K.edgeSet := by
  classical
  let P : SimpleGraph V → Prop := fun H =>
    G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H
  have hP : ∃ H : SimpleGraph V, P H := ⟨G, le_rfl, hdraw⟩
  obtain ⟨H, hH, hmax⟩ :=
    Set.exists_max_image {H : SimpleGraph V | P H}
      (fun H => Set.ncard H.edgeSet)
      (Set.toFinite {H : SimpleGraph V | P H})
      (by
        obtain ⟨H, hH⟩ := hP
        exact ⟨H, hH⟩)
  refine ⟨H, hH.1, hH.2, ?_⟩
  intro K hGK hKdraw
  exact hmax K ⟨hGK, hKdraw⟩