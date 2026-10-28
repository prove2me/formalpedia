-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_planar_supergraph_cda78d6a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:33:14.365859+00:00
-- url     : https://prove2.me/submissions/35b70315-0a5e-400a-b5fb-66a8e26b3d1b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ Q : SimpleGraph V,
      K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
        ∀ R : SimpleGraph V,
          Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => K ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hDrawing⟩⟩
  obtain ⟨hPQ, hQ⟩ : K ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have h2 := Finset.card_lt_card h1
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
