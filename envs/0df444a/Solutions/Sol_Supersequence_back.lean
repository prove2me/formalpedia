-- Prove2me | solution 1 for Supersequence.back
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:48.395684+00:00
-- url     : https://prove2.me/submissions/4694e113-efa2-4ce0-8341-abaea0d5c90c

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self
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
variable [DecidableEq α]
omit [DecidableEq α]
namespace Supersequence
theorem _root_.solution {x : α} {l g : List α} (hg : x ∉ g)
    (hw : Covers (fun _ => True) (l ++ g)) : Covers (· ≠ x) l := by
  intro q hn hq
  have h := hw (q ++ [x]) (by simp [nodup_append,hn]; grind) (by simp)
  exact (splitAtRequest h).resolve_right (fun hm => hg (singleton_sublist.mp hm))
end Supersequence
