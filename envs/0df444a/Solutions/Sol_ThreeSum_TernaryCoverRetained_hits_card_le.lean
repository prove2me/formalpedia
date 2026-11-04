-- Prove2me | solution 1 for ThreeSum.TernaryCoverRetained.hits_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:46:13.232177+00:00
-- url     : https://prove2.me/submissions/6a48fdcd-a7a9-499a-a186-908923c55e21

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained

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
    (hleft : ∀ e, left e ∈ VL) (hright : ∀ e, right e ∈ VR) (a b : K) :
    (hits left right hashL hashR a b).card ≤
      (bucket VL hashL a).card * (bucket VR hashR b).card := by
  classical
  have hcount : (hits left right hashL hashR a b).card ≤
      (bucket VL hashL a ×ˢ bucket VR hashR b).card := by
    apply card_le_card_of_injOn (fun e => (left e, right e))
    · intro e he
      obtain ⟨hl, hr⟩ := (mem_filter.mp he).2
      exact mem_product.mpr
        ⟨mem_filter.mpr ⟨hleft e, hl⟩, mem_filter.mpr ⟨hright e, hr⟩⟩
    · intro e _ f _ h
      exact hinj h
  simpa only [card_product] using hcount
end ThreeSum.TernaryCoverRetained
