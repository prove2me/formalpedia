-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_le_card_sym2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:39:13.611065+00:00
-- url     : https://prove2.me/submissions/75a68a80-4c36-487d-9457-3aa303d03b65

import Mathlib
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) : G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
  classical
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _)
