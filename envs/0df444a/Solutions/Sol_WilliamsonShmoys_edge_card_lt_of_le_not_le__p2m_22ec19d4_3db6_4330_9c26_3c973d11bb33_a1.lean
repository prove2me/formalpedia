-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:51:30.750199+00:00
-- url     : https://prove2.me/submissions/1acf507b-260c-4f12-9bce-914c1687c911

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L H : SimpleGraph V) [DecidableRel L.Adj] [DecidableRel H.Adj]
    (hLH : L ≤ H) (hnot : ¬ H ≤ L) :
    L.edgeFinset.card < H.edgeFinset.card := by
  classical
  have hne : L ≠ H := by
    intro heq
    apply hnot
    rw [heq]
  have hsub : L.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hLH
  have hneF : L.edgeFinset ≠ H.edgeFinset := by
    intro heq
    exact hne (SimpleGraph.edgeFinset_inj.mp heq)
  have hss : L.edgeFinset ⊂ H.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneF⟩
  exact Finset.card_lt_card hss
