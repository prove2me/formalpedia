-- Prove2me | solution 1 for WilliamsonShmoys.exists_connected_extension_of_local_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:51:53.046275+00:00
-- url     : https://prove2.me/submissions/2a163794-39af-43a9-8183-1cb272c6ce1d

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hStep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
        ∃ u v : V, L.Adj u v ∧ ¬ K.Adj u v)
    (H : SimpleGraph V) (hP : P H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ P G ∧ G.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => H ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hP⟩⟩
  obtain ⟨hHQ, hQ⟩ : H ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hHQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨L, hQL, hPL, u, v, hL, hnQ⟩ := hStep Q hQ hc
  have hne : Q ≠ L := fun h => hnQ (h ▸ hL)
  have hlt : Q < L := lt_of_le_of_ne hQL hne
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax L (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHQ.trans hQL, hPL⟩)
  omega
