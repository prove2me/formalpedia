-- Prove2me | solution 1 for Supersequence.cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:19.267748+00:00
-- url     : https://prove2.me/submissions/ddf1f488-3be4-4b54-b2d5-aa4e25cd9f7b

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_skipGap
section
namespace Supersequence
open List
variable {α : Type}
private theorem splitAtRequest {u v l r : List α} (h : (u ++ v).Sublist (l ++ r)) :
    u.Sublist l ∨ v.Sublist r := by
  obtain ⟨i,j,e,hi,hj⟩ := sublist_append_iff.mp h
  rcases append_eq_append_iff.mp e with ⟨k,hk,_⟩ | ⟨k,_,hk⟩
  · exact .inl ((sublist_append_left u k).trans (hk ▸ hi))
  · subst j
    exact .inr ((sublist_append_right k v).trans hj)
variable [DecidableEq α]
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
namespace Supersequence
theorem _root_.solution {x : α} {u v l g r : List α} (hx : x ∉ g)
    (h : (u ++ x :: v).Sublist (l ++ (g ++ r))) : u.Sublist l ∨ v.Sublist r := by
  rcases splitAtRequest h with hl | hr
  · exact .inl hl
  · exact .inr (sublist_of_cons_sublist (skipGap hx hr))
end Supersequence
