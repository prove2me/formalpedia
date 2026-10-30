-- Prove2me | solution 1 for WilliamsonShmoys.bridgeAddDisconnectedPair__p2m_f215bd68_2d93_43b9_b08b_d2556e5d1303_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:50:21.705546+00:00
-- url     : https://prove2.me/submissions/28fd5758-12c4-4e2d-8b5b-c458116c0db5

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (huv : u < v)
    (hreach : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      (∀ x y, H.Adj x y ↔
        G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧
      H.Adj u v ∧ ¬ G.Adj u v := by
  let H := G ⊔ SimpleGraph.fromRel (fun x y => x = u ∧ y = v)
  refine ⟨H, le_sup_left, ?_, ?_, ?_⟩
  · intro x y
    change (G ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).Adj x y ↔ _
    rw [SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]
    constructor
    · rintro (hG | ⟨_, hpair⟩)
      · exact Or.inl hG
      · rcases hpair with hpair | hpair
        · exact Or.inr (Or.inl hpair)
        · exact Or.inr (Or.inr ⟨hpair.2, hpair.1⟩)
    · rintro (hG | hpair | hpair)
      · exact Or.inl hG
      · rcases hpair with ⟨rfl, rfl⟩
        exact Or.inr ⟨huv.ne, Or.inl ⟨rfl, rfl⟩⟩
      · rcases hpair with ⟨rfl, rfl⟩
        exact Or.inr ⟨huv.ne.symm, Or.inr ⟨rfl, rfl⟩⟩
  · change (G ⊔ SimpleGraph.fromRel (fun a b => a = u ∧ b = v)).Adj u v
    rw [SimpleGraph.sup_adj]
    apply Or.inr
    rw [SimpleGraph.fromRel_adj]
    exact ⟨huv.ne, Or.inl ⟨rfl, rfl⟩⟩
  · intro hadj
    exact hreach hadj.reachable