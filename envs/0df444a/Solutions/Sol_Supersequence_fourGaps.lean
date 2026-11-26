-- Prove2me | solution 1 for Supersequence.fourGaps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:08.141792+00:00
-- url     : https://prove2.me/submissions/78ad59ae-bccf-4a90-9b01-c364dbe0400c

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_project_free
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self
section
namespace Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
private theorem decompose (x : α) (w : List α) :
    ∃ gs t, w = runs x gs ++ t ∧ x ∉ t ∧ ∀ g ∈ gs, x ∉ g := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons a w ih =>
    obtain ⟨gs,t,rfl,ht,hg⟩ := ih
    by_cases e : a = x
    · subst a; exact ⟨[] :: gs,t,by simp [runs],ht,by simpa using hg⟩
    · cases gs with
      | nil => exact ⟨[], a :: t, rfl, by simp [Ne.symm e,ht], by simp⟩
      | cons g gs =>
        exact ⟨(a::g) :: gs,t,rfl,ht,by
          intro v hv
          rcases mem_cons.mp hv with rfl | hv
          · simp [Ne.symm e,hg _ (.head _)]
          · exact hg _ (.tail _ hv)⟩
private theorem runs_account {x : α} {gs : List (List α)}
    (free : ∀ g ∈ gs, x ∉ g) :
    (runs x gs).count x = gs.length ∧
    (project x (runs x gs)).length = (gs.map List.length).sum := by
  induction gs with
  | nil => simp [runs,project]
  | cons g gs ih =>
    have ⟨hc,hl⟩ := ih (fun a ha => free a (.tail _ ha))
    have hf := project_free (free g (.head _))
    change (g ++ [x] ++ runs x gs).count x = _ ∧ (project x (g ++ [x] ++ runs x gs)).length = _
    simp [count_eq_zero.mpr (free g (.head _)),hc,hf,hl,project_cons_self]
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution {x : α} {w : List α} (hw : w.count x = 4) :
    ∃ a b c d e : List α, w = a ++ x :: (b ++ x :: (c ++ x :: (d ++ x :: e))) ∧
      x ∉ a ∧ x ∉ b ∧ x ∉ c ∧ x ∉ d ∧ x ∉ e := by
  obtain ⟨gs,t,ew,ht,hg⟩ := decompose x w
  have len : gs.length = 4 := by
    rwa [ew,count_append,(runs_account hg).1,count_eq_zero.mpr ht,Nat.add_zero] at hw
  rcases gs with _|⟨a,gs⟩ <;> simp at len
  rcases gs with _|⟨b,gs⟩ <;> simp at len
  rcases gs with _|⟨c,gs⟩ <;> simp at len
  rcases gs with _|⟨d,gs⟩ <;> simp at len
  subst gs
  exact ⟨a,b,c,d,t,by simpa [runs,append_assoc] using ew, by simpa [ht] using hg⟩
end Supersequence
