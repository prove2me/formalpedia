-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_mono__p2m_cd005786_48c0_47b3_9c83_f93270ee4ea9_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:16:28.213965+00:00
-- url     : https://prove2.me/submissions/3bff33e1-7634-4a7b-bd42-36e9a7b475b0

import Mathlib

set_option linter.unusedVariables false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hsub : forall u v, G.Adj u v -> H.Adj u v) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    G.edgeFinset.card <= H.edgeFinset.card := by
  classical
  have hGH : G ≤ H := by
    intro x y hxy
    exact hsub x y hxy
  apply Finset.card_le_card
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  exact SimpleGraph.edgeSet_mono hGH he
