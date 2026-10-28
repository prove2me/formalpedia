-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_supergraph_with_edge_lower_bound_completion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:46:43.333999+00:00
-- url     : https://prove2.me/submissions/18ec0f48-d0c8-42fe-8b38-66787094ed39

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ Z : SimpleGraph V, M ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      (∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => M ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hM⟩⟩
  obtain ⟨hPQ, hQ⟩ : M ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (fun h => hne (h ▸ le_rfl))
  have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have h2 := Finset.card_lt_card h1
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
