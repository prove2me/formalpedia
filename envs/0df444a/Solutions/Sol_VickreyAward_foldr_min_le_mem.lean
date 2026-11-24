-- Prove2me | solution 1 for VickreyAward.foldr_min_le_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:57.930426+00:00
-- url     : https://prove2.me/submissions/38ee8fa4-5b45-4087-b3cb-6c3e1f2e84a2


import Definitions.Def_VickreyTruthful

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r : Nat) : ∀ (l : List Nat) (x : Nat), x ∈ l → l.foldr min r ≤ x
  | [], _, h => absurd h (List.not_mem_nil)
  | y :: l, x, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := solution r l x h
        omega
end VickreyAward
