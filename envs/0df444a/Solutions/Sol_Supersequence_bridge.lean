-- Prove2me | solution 1 for Supersequence.bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:47.162867+00:00
-- url     : https://prove2.me/submissions/de40dd95-61c6-4d4b-a42e-25bbee44cbca

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_cut
section
namespace Supersequence
open List
variable {α : Type}
private theorem insertPivot {x : α} {u v : List α} (hn : (u ++ v).Nodup)
    (hx : x ∉ u ++ v) : (u ++ x :: v).Nodup := by
  simp only [nodup_append, nodup_cons, mem_cons, mem_append] at *
  grind
variable [DecidableEq α]
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
namespace Supersequence
theorem _root_.solution {x : α} {l g r alphabet : List α} (hx : x ∉ g)
    (letters : ∀ a, a ≠ x → a ∈ alphabet)
    (h : Covers (fun _ => True) (l ++ (g ++ r))) :
    Covers (fun a => a ≠ x) (l ++ (alphabet ++ r)) := by
  intro q hn hq
  suffices go : ∀ (tail pre : List α), q = pre ++ tail → pre.Sublist l →
      q.Sublist (l ++ (alphabet ++ r)) by
    exact go q [] rfl (nil_sublist _)
  intro tail
  induction tail with
  | nil =>
    intro pre he hl
    simpa [he] using (sublist_append_of_sublist_left (l₂ := alphabet ++ r) hl)
  | cons a t ih =>
    intro pre he hl
    by_cases ht : (pre ++ [a]).Sublist l
    · exact ih (pre ++ [a]) (by simpa [append_assoc] using he) ht
    · have he' : q = (pre ++ [a]) ++ t := by simpa [append_assoc] using he
      have hxq : x ∉ q := fun mem => hq x mem rfl
      have hp := insertPivot (x := x) (he' ▸ hn) (he' ▸ hxq)
      have hr := (cut hx (h _ hp (by simp))).resolve_left ht
      have ha : a ∈ q := by simp [he]
      have one : [a].Sublist alphabet := singleton_sublist.mpr (letters a (hq a ha))
      simpa [he, append_assoc] using hl.append (one.append hr)
end Supersequence
