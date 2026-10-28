-- Prove2me | solution 1 for WilliamsonShmoys.finite_graph_augmentation_of_strict_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:54:08.09395+00:00
-- url     : https://prove2.me/submissions/ba194505-0a71-4996-b08d-72ba73e3e407

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (D : SimpleGraph V → Prop)
    (P : SimpleGraph V)
    (hP : D P)
    (hStep : ∀ G : SimpleGraph V, D G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ D H) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧ D Q := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun G : SimpleGraph V => P ≤ G ∧ D G)).exists_max_image
    (fun G => G.edgeFinset.card) ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hP⟩⟩
  obtain ⟨hTQ, hQ⟩ : P ≤ Q ∧ D Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, hTQ, ?_, hQ⟩
  by_contra hc
  obtain ⟨R, hlt, hR⟩ := hStep Q hQ hc
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTQ.trans hlt.le, hR⟩)
  omega
