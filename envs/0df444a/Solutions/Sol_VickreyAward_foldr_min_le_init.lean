-- Prove2me | solution 1 for VickreyAward.foldr_min_le_init
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:57.241036+00:00
-- url     : https://prove2.me/submissions/8284360c-7758-4839-94f6-27953dc976ca


import Definitions.Def_VickreyTruthful

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r : Nat) : ∀ l : List Nat, l.foldr min r ≤ r
  | [] => Nat.le_refl r
  | x :: l => by
      simp only [List.foldr_cons]
      have := solution r l
      omega
end VickreyAward
