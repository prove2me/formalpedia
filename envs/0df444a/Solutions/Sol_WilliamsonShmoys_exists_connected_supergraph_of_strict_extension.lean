-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_supergraph_of_strict_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:38:23.597418+00:00
-- url     : https://prove2.me/submissions/a36a4c8d-3cdc-436c-a5db-5c9add61b69d

import Mathlib
set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hPK : P K)
    (hstep : ∀ G, K ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ H.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => K ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hPK⟩⟩
  obtain ⟨hKQ, hQ⟩ : K ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hKQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨R, hlt, hR⟩ := hstep Q hKQ hQ hc
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKQ.trans hlt.le, hR⟩)
  omega
