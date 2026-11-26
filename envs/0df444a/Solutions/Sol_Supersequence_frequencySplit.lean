-- Prove2me | solution 1 for Supersequence.frequencySplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:00:05.26733+00:00
-- url     : https://prove2.me/submissions/194001b1-0a43-44a0-b039-e585cd0ea916

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_projected_bound
import Theorems.Thm_Supersequence_front
import Theorems.Thm_Supersequence_length_account
import Theorems.Thm_Supersequence_pivotInequality
import Theorems.Thm_Supersequence_universal_iff_covers
import Theorems.Thm_Supersequence_transportNine
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution (nine : ∀ v : List (Fin 9), Universal v → 66 ≤ v.length)
    {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82) :
    (∀ x, 4 ≤ w.count x) ∧ (∃ x, w.count x ≤ 7) := by
  have cover := universal_iff_covers.mp hw
  constructor
  · intro x
    let A := (finRange 10).erase x
    have ha : A.length = 9 := by simp [A,length_erase_of_mem (mem_finRange x)]
    have h := pivotInequality (x := x) (alphabet := A) cover (transportNine nine x)
      (fun a ne => (mem_erase_of_ne ne).mpr (mem_finRange a))
    rw [ha] at h
    have account := length_account x w
    rcases Nat.lt_or_ge (w.count x) 4 with small | large
    · have cases : w.count x = 0 ∨ w.count x = 1 ∨ w.count x = 2 ∨ w.count x = 3 := by omega
      rcases cases with e|e|e|e <;> rw [e] at h account <;> omega
    · exact large
  · let p := w.take 9
    let r := w.drop 9
    have plen : p.length = 9 := by simp [p,len]
    have missing : ∃ x : Fin 10, x ∉ p := by
      apply Classical.byContradiction
      intro no
      have sub : finRange 10 ⊆ p := fun a _ => Classical.byContradiction (fun h => no ⟨a,h⟩)
      have := (nodup_finRange 10).length_le_of_subset sub
      simp [plen] at this
    obtain ⟨x,hx⟩ := missing
    have eq : w = p ++ r := (take_append_drop _ _).symm
    have h := projected_bound (transportNine nine x) (front hx (eq ▸ cover))
    have account := length_account x r
    have count : w.count x = r.count x := by rw [eq,count_append,count_eq_zero.mpr hx,Nat.zero_add]
    have total : w.length = p.length + r.length := by rw [eq,length_append]
    exact ⟨x,by omega⟩
end Supersequence
