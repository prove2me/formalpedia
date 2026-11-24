-- Prove2me | solution 1 for VickreyAward.cost_le_price_of_wins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:37.224829+00:00
-- url     : https://prove2.me/submissions/e90c41a2-d499-409e-8c25-e957dc70c4a4


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_le_foldr_min

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution {r c : Nat} {before after : List Nat}
    (h : wins r before after c) : c ≤ price r before after := by
  obtain ⟨hr, hb, ha⟩ := h
  apply le_foldr_min r c hr
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Nat.le_of_lt (hb x hx)
  · exact ha x hx
end VickreyAward
