-- Prove2me | solution 1 for Supersequence.universal_iff_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:45.747858+00:00
-- url     : https://prove2.me/submissions/7224a8da-1faf-4a6e-a1f4-0edf35fab8f0

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution {w : List (Fin n)} :
    Universal w ↔ Covers (fun _ => True) w := by
  constructor
  · intro h q hq _
    let rest := (finRange n).filter (fun a => !q.contains a)
    have dis : (q ++ rest).Nodup := by
      apply nodup_append.mpr
      refine ⟨hq,(nodup_finRange n).sublist (filter_sublist),?_⟩
      intro a ha b hb eq
      simp [rest,← eq,ha] at hb
    have all : ∀ a, a ∈ q ++ rest := by
      intro a
      by_cases ha : a ∈ q <;> simp [rest,ha,mem_finRange]
    have hp : (q ++ rest).Perm (finRange n) := by
      apply perm_iff_count.mpr
      intro a
      rw [dis.count, (nodup_finRange n).count, if_pos (all a), if_pos (mem_finRange a)]
    exact (sublist_append_left q rest).trans (h _ hp)
  · intro h p hp
    exact h p (hp.nodup_iff.mpr (nodup_finRange n)) (by simp)
end Supersequence
