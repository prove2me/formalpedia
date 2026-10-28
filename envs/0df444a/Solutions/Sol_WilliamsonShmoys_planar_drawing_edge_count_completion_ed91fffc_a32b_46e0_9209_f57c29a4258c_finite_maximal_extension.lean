-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_finite_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:48:28.147205+00:00
-- url     : https://prove2.me/submissions/ed4f5cf9-1b3d-4dbc-9f06-d78103c46c6a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ R : SimpleGraph V,
      G ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S →
        WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ R := by
  classical
  obtain ⟨P, hPm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => G ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hQP, hP⟩ : G ≤ P ∧ HasPlanarDrawingOn P := (Finset.mem_filter.mp hPm).2
  refine ⟨P, hQP, hP, fun R hPR hR => ?_⟩
  by_contra hne
  have hlt : P < R := lt_of_le_of_ne hPR (fun h => hne (h ▸ le_rfl))
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQP.trans hPR, hR⟩)
  omega
