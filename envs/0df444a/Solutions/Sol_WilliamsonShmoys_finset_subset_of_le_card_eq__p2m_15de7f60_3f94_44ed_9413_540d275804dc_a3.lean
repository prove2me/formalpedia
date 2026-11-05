-- Prove2me | solution 1 for WilliamsonShmoys.finset_subset_of_le_card_eq__p2m_15de7f60_3f94_44ed_9413_540d275804dc_a3
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:07:02.662925+00:00
-- url     : https://prove2.me/submissions/c82a0b16-ad6a-41a6-97ff-6abcacd10d5c

import Mathlib

theorem solution {α : Type} [DecidableEq α] (s t : Finset α)
    (hst : s ⊆ t) (hcard : t.card ≤ s.card) : s = t := by
  exact Finset.eq_of_subset_of_card_le hst hcard
