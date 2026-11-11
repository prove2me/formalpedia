-- Prove2me | solution 1 for WilliamsonShmoys.exists_max_card_simpleGraph__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:12:18.3517+00:00
-- url     : https://prove2.me/submissions/77ec4363-fbfb-4580-a0d9-657c298fd6d6

import Mathlib

set_option autoImplicit false

/-- Among all graphs satisfying `P`, one with the maximal number of edges exists. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop)
    (G₀ : SimpleGraph V) (h₀ : P G₀) :
    ∃ G : SimpleGraph V, P G ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       ∀ H : SimpleGraph V, P H →
        letI : DecidableRel H.Adj := Classical.decRel H.Adj
        H.edgeFinset.card ≤ G.edgeFinset.card) := by
  classical
  let f : SimpleGraph V → ℕ := fun G =>
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card
  let s : Finset (SimpleGraph V) := Finset.univ.filter P
  have hs : s.Nonempty := ⟨G₀, by simp [s, h₀]⟩
  obtain ⟨G, hG, hmax⟩ := Finset.exists_max_image s f hs
  refine ⟨G, ?_, ?_⟩
  · simpa [s] using hG
  · intro H hH
    exact hmax H (by simp [s, hH])
