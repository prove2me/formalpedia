-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:17:56.325694+00:00
-- url     : https://prove2.me/submissions/e86fe7aa-332d-4831-b67f-178120e84001

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧
      H.edgeSet.ncard ≤ L.edgeSet.ncard ∧
      P L ∧
      ∀ K : SimpleGraph V, L ≤ K → P K → K = L := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => H ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  have key : ∀ R : SimpleGraph V, Q ≤ R → P R → R = Q := by
    intro R hQR hR
    by_contra hne
    have hlt : Q < R := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  exact ⟨Q, hPQ, Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ) (Set.toFinite _), hQ, key⟩
