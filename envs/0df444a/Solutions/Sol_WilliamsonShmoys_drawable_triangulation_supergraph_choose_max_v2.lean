-- Prove2me | solution 1 for WilliamsonShmoys.drawable_triangulation_supergraph_choose_max_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:26:53.33782+00:00
-- url     : https://prove2.me/submissions/49df3c0e-c8e5-4a45-ab9c-cd15db7e366a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false
theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => K ≤ X0 ∧ HasPlanarDrawingOn X0)).exists_max_image
    (fun X0 => X0.edgeSet.ncard) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  exact ⟨Q, hPQ, hQ, fun M h1 h2 => hmax M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)⟩
