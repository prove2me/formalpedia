-- Prove2me | solution 1 for Supersequence.heavyLetter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:59.813477+00:00
-- url     : https://prove2.me/submissions/73f067b7-a65f-429e-ba85-06b0d9ef4ecd

import Definitions.Def_Frequency
import Definitions.Def_Four
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_skipGap
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self


section
namespace Supersequence
open List
variable {α : Type} [DecidableEq α]
omit [DecidableEq α] in
private theorem largest (f : α → Nat) {A : List α} (ha : A ≠ []) :
    ∃ a ∈ A, ∀ b ∈ A, f b ≤ f a := by
  induction A with
  | nil => contradiction
  | cons a t ih =>
    by_cases ht : t = []
    · subst t; simp
    · obtain ⟨b,hb,hm⟩ := ih ht
      by_cases h : f a ≤ f b
      · exact ⟨b,.tail _ hb,by intro c hc; rcases mem_cons.mp hc with rfl|hh <;> grind⟩
      · exact ⟨a,.head _,by intro c hc; rcases mem_cons.mp hc with rfl|hh <;> grind⟩
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]
namespace Supersequence
theorem _root_.solution {A w : List α} (nd : A.Nodup) (nonempty : A ≠ [])
    (cov : Covers (· ∈ A) w) : ∃ a ∈ A, A.length ≤ w.count a := by
  obtain ⟨x,hx,maximal⟩ := largest (fun a => w.idxOf a) nonempty
  have xw : x ∈ w := singleton_sublist.mp (cov [x] (by simp) (by simpa using hx))
  obtain ⟨p,t,ew,hp⟩ := eq_append_cons_of_mem xw
  let B := A.erase x
  have bl : B.length = A.length-1 := length_erase_of_mem hx
  by_cases empty : B = []
  · exact ⟨x,hx,by have := count_pos_iff.mpr xw; simp [empty] at bl; omega⟩
  have tail : Covers (· ∈ B) t := by
    intro q hn hq
    have xq : x ∉ q := fun h => nd.not_mem_erase (hq x h)
    have hh := cov (x::q) (by simp [xq,hn]) (by
      intro a ha; rcases mem_cons.mp ha with rfl | h
      · exact hx
      · exact erase_subset (hq a h))
    rw [ew] at hh
    exact cons_sublist_cons.mp (skipGap hp hh)
  obtain ⟨a,ha,freq⟩ := solution (nd.erase x) empty tail
  have ne : a ≠ x := fun e => nd.not_mem_erase (e ▸ ha)
  have aa : a ∈ A := erase_subset ha
  have ap : a ∈ p := by
    apply Classical.byContradiction
    intro miss
    have h := maximal a aa
    have hne1 : (x == a) = false := beq_eq_false_iff_ne.mpr (Ne.symm ne)
    have hne2 : (a == x) = false := beq_eq_false_iff_ne.mpr ne
    simp [ew,idxOf_append,hp,miss,idxOf_cons,hne1,hne2] at h; omega
  change B.length ≤ t.count a at freq
  exact ⟨a,aa,by have := count_pos_iff.mpr ap; rw [ew,count_append,count_cons]; omega⟩
termination_by A.length
decreasing_by rw [length_erase_of_mem hx]; have := length_pos_iff.mpr nonempty; omega
end Supersequence
