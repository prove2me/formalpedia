-- Prove2me | solution 1 for WilliamsonShmoys.connectedComponent_edge_conservation__p2m_1c5fc6d8_f74d_4a49_af67_c6124a04288f_a1
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-17T09:39:20.821474+00:00
-- url     : https://prove2.me/submissions/7a9568f6-6559-4835-ab63-5d6eb4fec9da

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hpair : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s),
    (letI : DecidableRel L.Adj := dL;
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card)) := by
  intro H
  have h := @H (Fin 3) _ _ ⊤ inferInstance {Finset.univ, {0, 1}}
    (fun u v _ => ⟨Finset.univ, by simp, by simp, by simp⟩)
  revert h
  decide
