-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_strict_of_lt__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:48:37.283519+00:00
-- url     : https://prove2.me/submissions/fb683c2f-2bce-4b61-8cbe-9654d8eb9053

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype H.edgeSet]
    (hGH : LE.le G H) (hne : G ≠ H) : G.edgeFinset.card < H.edgeFinset.card := by
  classical
  have hsub : G.edgeFinset ⊆ H.edgeFinset := SimpleGraph.edgeFinset_mono hGH
  have hneF : G.edgeFinset ≠ H.edgeFinset := by
    intro heq
    exact hne (SimpleGraph.edgeFinset_inj.mp heq)
  have hss : G.edgeFinset ⊂ H.edgeFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hneF⟩
  exact Finset.card_lt_card hss
