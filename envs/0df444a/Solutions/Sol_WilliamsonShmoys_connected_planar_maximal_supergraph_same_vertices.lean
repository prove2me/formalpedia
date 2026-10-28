-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_maximal_supergraph_same_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:29:14.81118+00:00
-- url     : https://prove2.me/submissions/4db59454-fb89-46fb-bf30-65961639e850

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hdraw⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hPQ, hQ, hconn.mono hPQ, fun R hQR hR => ?_⟩
  by_contra hne
  have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
  omega
