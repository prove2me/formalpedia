-- Prove2me | solution 1 for VickreyAward.truthful_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:46.454128+00:00
-- url     : https://prove2.me/submissions/52a03c4d-29a6-48b2-b4e9-922dd88145de


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_cost_le_price_of_wins

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r : Nat) (before after : List Nat) (c : Nat) :
    0 ≤ utility r before after c c := by
  unfold utility
  by_cases hc : wins r before after c <;> simp only [hc, ite_true, ite_false]
  · have := cost_le_price_of_wins hc
    omega
  · exact Int.le_refl _
end VickreyAward
