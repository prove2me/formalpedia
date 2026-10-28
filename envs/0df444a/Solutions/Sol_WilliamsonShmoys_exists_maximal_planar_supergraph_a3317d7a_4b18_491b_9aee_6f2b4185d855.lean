-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_a3317d7a_4b18_491b_9aee_6f2b4185d855
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:30:50.460396+00:00
-- url     : https://prove2.me/submissions/b0be1db0-8567-49e0-bbee-bf2178fd1cc0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      LE.le Y Z ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z ∧
      ∀ W : SimpleGraph V,
        LE.le Z W →
        WilliamsonShmoys.HasPlanarDrawingOn W →
        W = Z := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => Y ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨Y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hY⟩⟩
  obtain ⟨hPQ, hQ⟩ : Y ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have h2 := Finset.card_lt_card h1
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
