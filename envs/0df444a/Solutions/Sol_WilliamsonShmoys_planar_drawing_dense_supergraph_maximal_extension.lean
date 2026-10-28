-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_dense_supergraph_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:57:36.79852+00:00
-- url     : https://prove2.me/submissions/74ec1907-0fb8-4b1f-bb98-51ae59a90367

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V,
      R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T →
        WilliamsonShmoys.HasPlanarDrawingOn T → T ≤ S := by
  classical
  obtain ⟨P, hPm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => R ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hR⟩⟩
  obtain ⟨hQP, hP⟩ : R ≤ P ∧ HasPlanarDrawingOn P := (Finset.mem_filter.mp hPm).2
  refine ⟨P, hQP, hP, fun T hPR hT => ?_⟩
  by_contra hne
  have hlt : P < T := lt_of_le_of_ne hPR (fun h => hne (h ▸ le_rfl))
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQP.trans hPR, hT⟩)
  omega
