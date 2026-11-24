-- Prove2me | solution 1 for VickreyAward.truthful_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:44.193271+00:00
-- url     : https://prove2.me/submissions/7202e62d-d24b-42fa-9a58-268c0087f02c


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_cost_le_price_of_wins
import Theorems.Thm_VickreyAward_price_le_cost_of_not_wins

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r : Nat) (before after : List Nat) (c b : Nat) :
    utility r before after c b ≤ utility r before after c c := by
  unfold utility
  by_cases hc : wins r before after c <;> by_cases hb : wins r before after b <;>
    simp only [hc, hb, ite_true, ite_false]
  · exact Int.le_refl _
  · have := cost_le_price_of_wins hc
    omega
  · have := price_le_cost_of_not_wins hc
    omega
  · exact Int.le_refl _
end VickreyAward
