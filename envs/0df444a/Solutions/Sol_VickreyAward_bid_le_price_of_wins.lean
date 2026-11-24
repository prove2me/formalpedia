-- Prove2me | solution 1 for VickreyAward.bid_le_price_of_wins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:26:45.524549+00:00
-- url     : https://prove2.me/submissions/13a447cd-b5d0-4238-9a81-ef28b7e6d412


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_cost_le_price_of_wins

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution {r b : Nat} {before after : List Nat}
    (h : wins r before after b) : b ≤ price r before after :=
  cost_le_price_of_wins h
end VickreyAward
