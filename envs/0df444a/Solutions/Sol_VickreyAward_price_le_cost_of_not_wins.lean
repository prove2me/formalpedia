-- Prove2me | solution 1 for VickreyAward.price_le_cost_of_not_wins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:18.278514+00:00
-- url     : https://prove2.me/submissions/c80b145d-ff03-4943-ba53-077bbea014d0


import Definitions.Def_VickreyTruthful
import Theorems.Thm_VickreyAward_foldr_min_le_init
import Theorems.Thm_VickreyAward_foldr_min_le_mem

set_option autoImplicit true
open VickreyAward
namespace VickreyAward
theorem _root_.solution {r c : Nat} {before after : List Nat}
    (h : ¬ wins r before after c) : price r before after ≤ c := by
  unfold wins at h
  unfold price
  by_cases hr : c ≤ r
  · by_cases hb : ∀ x ∈ before, c < x
    · -- some later bidder bid strictly below c
      have : ¬ ∀ x ∈ after, c ≤ x := fun ha => h ⟨hr, hb, ha⟩
      obtain ⟨x, hx, hlt⟩ : ∃ x ∈ after, ¬ c ≤ x := by
        apply Classical.byContradiction
        intro hne
        exact this (fun x hx => Classical.byContradiction (fun hn => hne ⟨x, hx, hn⟩))
      have := foldr_min_le_mem r (before ++ after) x (List.mem_append_right _ hx)
      omega
    · -- some earlier bidder bid at or below c
      obtain ⟨x, hx, hle⟩ : ∃ x ∈ before, ¬ c < x := by
        apply Classical.byContradiction
        intro hne
        exact hb (fun x hx => Classical.byContradiction (fun hn => hne ⟨x, hx, hn⟩))
      have := foldr_min_le_mem r (before ++ after) x (List.mem_append_left _ hx)
      omega
  · -- the cost is above the reserve, and the price never is
    have := foldr_min_le_init r (before ++ after)
    omega
end VickreyAward
