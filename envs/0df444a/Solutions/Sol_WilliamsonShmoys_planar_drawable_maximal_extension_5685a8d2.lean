-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_maximal_extension_5685a8d2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:34:47.789806+00:00
-- url     : https://prove2.me/submissions/df25a6ea-2eeb-47b3-af09-489e5c9a34a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet ∧
      HasPlanarDrawingOn G ∧
      ∀ K : SimpleGraph V,
        G.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K →
        K.edgeSet = G.edgeSet := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => H ≤ X0 ∧ WilliamsonShmoys.HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hDraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ, hQ, fun G h1 h2 =>
    congrArg SimpleGraph.edgeSet (key G (SimpleGraph.edgeSet_subset_edgeSet.mp h1) h2)⟩
