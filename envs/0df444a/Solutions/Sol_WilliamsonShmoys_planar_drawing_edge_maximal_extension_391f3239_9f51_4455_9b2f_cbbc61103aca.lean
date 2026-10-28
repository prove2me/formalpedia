-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T04:31:10.993407+00:00
-- url     : https://prove2.me/submissions/bbf9e490-73e9-47ac-92fd-d084c31b16ce

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun H : SimpleGraph V => G ≤ H ∧ HasPlanarDrawingOn H)).exists_max_image
    (fun H => H.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hPQ, hQ⟩ : G ≤ Q ∧ HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
