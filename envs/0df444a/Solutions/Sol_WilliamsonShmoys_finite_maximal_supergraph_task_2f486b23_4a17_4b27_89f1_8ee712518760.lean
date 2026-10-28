-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:15:01.928904+00:00
-- url     : https://prove2.me/submissions/ae8fea7c-8b1a-42b9-b15f-90abea1be5d2

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hH : P H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧
      P L ∧
      (∀ M : SimpleGraph V, L ≤ M → P M → M = L) := by
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
  exact ⟨Q, hPQ, hQ, key⟩
