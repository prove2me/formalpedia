-- Prove2me | solution 1 for ThreeSum.TernaryCoverRetained.hits_card_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:46:55.592666+00:00
-- url     : https://prove2.me/submissions/69b180bd-22b6-45ad-95ff-b6f176e19b9a

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Theorems.Thm_ThreeSum_TernaryCoverRetained_hits_card_le

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverRetained
open Finset
open scoped BigOperators
variable {E A B K : Type*} [Fintype E]
variable [DecidableEq A] [DecidableEq B] [DecidableEq K]
namespace ThreeSum.TernaryCoverRetained
theorem _root_.solution (left : E → A) (right : E → B)
    (hashL : A → K) (hashR : B → K) (VL : Finset A) (VR : Finset B)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR)
    (a b : K) (cap : ℕ)
    (hl : (bucket VL hashL a).card ≤ cap)
    (hr : (bucket VR hashR b).card ≤ cap) :
    (hits left right hashL hashR a b).card ≤ cap ^ 2 := by
  calc
    _ ≤ (bucket VL hashL a).card * (bucket VR hashR b).card :=
      hits_card_le left right hashL hashR VL VR hinj hleft hright a b
    _ ≤ cap * cap := Nat.mul_le_mul hl hr
    _ = cap ^ 2 := by rw [pow_two]
end ThreeSum.TernaryCoverRetained
