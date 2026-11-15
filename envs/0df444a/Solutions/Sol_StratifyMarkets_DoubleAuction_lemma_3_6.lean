-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:38:07.351999+00:00
-- url     : https://prove2.me/submissions/3a9fef88-2f84-4d7c-b689-35374cbd7200

import Mathlib
import Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_5

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_3_6
section
open StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) :
    ∃ M : OrderedMatching, 1 / 4 * I.roProfit ≤ I.orderedMatching M := by
  obtain ⟨⟨s, hs⟩, ⟨b, hb⟩⟩ := lemma_3_5 I
  unfold BTInstance.roProfit
  rcases le_total I.buyerProfit I.sellerProfit with h | h
  · exact ⟨s, by linarith⟩
  · exact ⟨b, by linarith⟩
end
