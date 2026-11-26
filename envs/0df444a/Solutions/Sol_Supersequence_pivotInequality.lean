-- Prove2me | solution 1 for Supersequence.pivotInequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:35.106009+00:00
-- url     : https://prove2.me/submissions/362a7971-af5e-4f6d-b8f4-965eae348736

import Std
import Definitions.Def_Frequency
import Theorems.Thm_Supersequence_bridge
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_project_free
import Theorems.Thm_Supersequence_projected_bound
import Theorems.Thm_Supersequence_front
import Theorems.Thm_Supersequence_back
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
omit [DecidableEq α] in
private theorem sum_le {gs : List (List α)} {B : Nat}
    (h : ∀ g ∈ gs, g.length ≤ B) : (gs.map List.length).sum ≤ gs.length * B := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun a ha => h a (.tail _ ha))
    have hh := h g (.head _)
    simp [Nat.succ_mul]; omega
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type}
variable [DecidableEq α]
namespace Supersequence
theorem _root_.solution {w alphabet : List α} {x : α} {F : Nat}
    (hw : Covers (fun _ => True) w) (low : LowerOnOthers x F)
    (letters : ∀ a, a ≠ x → a ∈ alphabet) :
    F + alphabet.length ≤ w.count x * ((project x w).length - F + alphabet.length) := by
  have present : x ∈ w := singleton_sublist.mp (hw [x] (by simp) (by simp))
  obtain ⟨p,y,ew,hp⟩ := eq_append_cons_of_mem present
  obtain ⟨gs,t,ey,ht,hg⟩ := decompose x y
  let T := (project x w).length
  let B := T - F
  have oldlen : F ≤ T := projected_bound low (fun q hn _ => hw q hn (by simp))
  have gap_bound (l g r : List α) (eqn : w = l ++ (g ++ r)) (free : x ∉ g) :
      g.length ≤ B + alphabet.length := by
    have h := projected_bound low (bridge free letters (eqn ▸ hw))
    have hlen : T = (project x l).length + (g.length + (project x r).length) := by
      simp only [T,eqn,project_append,project_free free,length_append]
    have ha := length_filter_le (· != x) alphabet
    simp only [project,filter_append,length_append] at h hlen
    unfold B; omega
  have left_bound : p.length ≤ B := by
    have h := projected_bound low (front hp (ew ▸ hw))
    have ht' : T = p.length + (project x (x::y)).length := by
      simp only [T,ew,project_append,project_free hp,length_append]
    unfold B; omega
  have eqt : w = (p ++ x :: runs x gs) ++ t := by simp [ew,ey,append_assoc]
  have right_bound : t.length ≤ B := by
    have h := projected_bound low (back ht (eqt ▸ hw))
    have ht' : T = (project x (p ++ x :: runs x gs)).length + t.length := by
      simp only [T,eqt,project_append,project_free ht,length_append]
    unfold B; omega
  have bound := sum_le (gs := gs) (B := B + alphabet.length) (by
    intro g mem
    obtain ⟨a,b,e⟩ := append_of_mem mem
    apply gap_bound (p ++ x :: runs x a) g (x :: (runs x b ++ t)) _ (hg g mem)
    simp [ew,ey,e,runs,append_assoc])
  obtain ⟨hc,hl⟩ := runs_account hg
  have count : w.count x = gs.length + 1 := by
    simp [eqt,count_eq_zero.mpr hp,count_eq_zero.mpr ht,hc]
  have len : T = p.length + (gs.map List.length).sum + t.length := by
    simp only [T,eqt,project_append,project_cons_self,project_free hp,project_free ht,length_append,hl]
  rw [count]
  change F + alphabet.length ≤ (gs.length + 1) * (B + alphabet.length)
  rw [Nat.add_mul, Nat.one_mul]
  have split : B + F = T := by dsimp [B]; omega
  omega
end Supersequence
