-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_eq_of_graph_eq__p2m_cd754a9f_7b3b_4f66_b68b_c9f75eba4801_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:22.078769+00:00
-- url     : https://prove2.me/submissions/0af918b5-de63-49dd-a164-294be84352cf

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (dG : DecidableRel G.Adj) (dH : DecidableRel H.Adj)
    (h : G = H) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
      (letI : DecidableRel H.Adj := dH; H.edgeFinset.card) := by
  subst H
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset]