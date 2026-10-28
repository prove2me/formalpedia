-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_predicate_extension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:37:59.413985+00:00
-- url     : https://prove2.me/submissions/69b3dad5-7d4f-4742-beaa-22f04eb393f3

import Mathlib
set_option autoImplicit false
theorem solution {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V, P K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, P L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        ∀ u v, L.Adj u v → K.Adj u v) := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => H ≤ G ∧ P G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hH⟩⟩
  obtain ⟨hPQ, hQ⟩ : H ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hQ, fun u v h => hPQ h, fun R hR hQR => ?_⟩
  have hQR' : Q ≤ R := fun u v h => hQR u v h
  by_contra hne
  push_neg at hne
  obtain ⟨u, v, huv, hn⟩ := hne
  have hlt : Q < R := lt_of_le_of_ne hQR' (fun h => hn (h ▸ huv))
  have h1 : Q.edgeFinset ⊂ R.edgeFinset := SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt
  have h2 := Finset.card_lt_card h1
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR', hR⟩)
  omega
