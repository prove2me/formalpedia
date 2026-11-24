-- Prove2me | solution 1 for VickreyAward.le_foldr_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:08.399895+00:00
-- url     : https://prove2.me/submissions/34b796de-6b12-4b43-8b79-2e0b895fc1c5


import Definitions.Def_VickreyTruthful

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution (r c : Nat) (hr : c ≤ r) :
    ∀ l : List Nat, (∀ x ∈ l, c ≤ x) → c ≤ l.foldr min r
  | [], _ => hr
  | y :: l, h => by
      simp only [List.foldr_cons]
      have hy := h y (List.mem_cons_self ..)
      have ih := solution r c hr l (fun x hx => h x (List.mem_cons_of_mem _ hx))
      omega
end VickreyAward
