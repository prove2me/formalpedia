-- Prove2me | solution 1 for VickreyAward.price_le_reserve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:20.356923+00:00
-- url     : https://prove2.me/submissions/8edb128e-5b15-44b2-8cf7-ae2a60ed2369


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_foldr_min_le_init

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r : Nat) (before after : List Nat) : price r before after ≤ r :=
  foldr_min_le_init r _
end VickreyAward
