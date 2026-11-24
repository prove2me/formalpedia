-- Prove2me | solution 1 for VickreyAward.wins_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:14.752316+00:00
-- url     : https://prove2.me/submissions/1450caff-56c1-4b26-9c25-e458f4504ce6


import Definitions.Def_VickreyTruthful

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution {r : Nat} {before after : List Nat} {b b' : Nat}
    (h : wins r before after b) (hle : b' ≤ b) : wins r before after b' := by
  obtain ⟨hr, hb, ha⟩ := h
  exact ⟨Nat.le_trans hle hr,
         fun x hx => Nat.lt_of_le_of_lt hle (hb x hx),
         fun x hx => Nat.le_trans hle (ha x hx)⟩
end VickreyAward
