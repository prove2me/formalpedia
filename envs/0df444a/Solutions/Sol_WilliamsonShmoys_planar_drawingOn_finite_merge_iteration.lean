-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_finite_merge_iteration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:06:10.131315+00:00
-- url     : https://prove2.me/submissions/84c07283-ccf6-499b-8f43-3dd361399f19

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hstep : ∀ (R : SimpleGraph V), P ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R → ¬ R.Connected →
      ∃ S : SimpleGraph V,
        R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
        (∀ u v, R.Reachable u v → S.Reachable u v) ∧
        ∃ u v, ¬ R.Reachable u v ∧ S.Reachable u v) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => P ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hTQ, hQ⟩ : P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hTQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨R, hle, hR, -, u, v, hnr, hr⟩ := hstep Q hTQ hQ hc
  have hlt : Q < R := lt_of_le_of_ne hle (by rintro rfl; exact hnr hr)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hlt.le, hR⟩)
  omega
