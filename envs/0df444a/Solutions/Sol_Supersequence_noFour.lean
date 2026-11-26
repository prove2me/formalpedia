-- Prove2me | solution 1 for Supersequence.noFour
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:31.777505+00:00
-- url     : https://prove2.me/submissions/684dc375-4473-4a45-8563-530d3808edc8

import Definitions.Def_Frequency
import Definitions.Def_Four
import Theorems.Thm_Supersequence_outerCutLength
import Theorems.Thm_Supersequence_back
import Theorems.Thm_Supersequence_bridge
import Theorems.Thm_Supersequence_complementaryCut
import Theorems.Thm_Supersequence_fourGaps
import Theorems.Thm_Supersequence_front
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_project_free
import Theorems.Thm_Supersequence_projected_bound
import Theorems.Thm_Supersequence_transportNine
import Theorems.Thm_Supersequence_universal_iff_covers
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self


section
namespace Supersequence
open List
variable {α : Type} [DecidableEq α]
omit [DecidableEq α] in
private theorem mono {P Q : α → Prop} {w : List α} (h : Covers P w)
    (sub : ∀ a, Q a → P a) : Covers Q w :=
  fun r hn mem => h r hn (fun a ha => sub a (mem a ha))
private theorem compatible_swap {A p q : List α} (h : Compatible A p q) : Compatible A q p := by
  intro S sub
  rcases h (rest A S) filter_sublist.subset with left | right
  · exact .inr left
  · exact .inl (mono right (by intro a mem; simp [rest,mem,sub mem]))
private theorem keep {x : α} {P : α → Prop} {w : List α} (h : Covers P w)
    (free : ∀ a, P a → a ≠ x) : Covers P (project x w) := by
  intro q hn hq
  have he := (h _ hn hq).filter (· != x)
  rwa [show q.filter (· != x) = q from project_free (fun m => free x (hq x m) rfl)] at he
private theorem projectedCut {x : Fin 10} {l g r : List (Fin 10)}
    (hg : x ∉ g) (hw : Covers (fun _ => True) (l ++ (g ++ r))) :
    Compatible ((finRange 10).erase x) (project x l) (project x r) := by
  intro S sub
  have ha (a : Fin 10) : a ∈ (finRange 10).erase x ↔ a ≠ x := by
    by_cases e : a=x
    · subst a; simp [(nodup_finRange 10).not_mem_erase]
    · simp [mem_erase_of_ne e,mem_finRange,e]
  rcases complementaryCut hg hw (· ∈ S) with left | right
  · exact .inl (mono (keep left (fun a h => h.1)) (fun a m => ⟨(ha a).mp (sub m),m⟩))
  · exact .inr (mono (keep right (fun a h => h.1)) (by
      intro a m; simpa [rest,ha] using m))
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]
namespace Supersequence
theorem _root_.solution {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66) :
    ∀ x, w.count x ≠ 4 := by
  intro x mult
  obtain ⟨a,b,c,d,e,eq,ha,hb,hc,hd,he⟩ := fourGaps mult
  have cover := universal_iff_covers.mp hw
  let A := (finRange 10).erase x
  have nd : A.Nodup := (nodup_finRange 10).erase x
  have nine : A.length = 9 := by simp [A,length_erase_of_mem (mem_finRange x)]
  have low := transportNine f9 x
  have total : a.length + b.length + c.length + d.length + e.length = 78 := by
    simp [eq] at len; omega
  have head := front (x := x) ha (eq ▸ cover)
  have left := projected_bound low head
  simp only [project_cons_self,project_append,project_free hb,project_free hc,
    project_free hd,project_free he,length_append] at left
  have eq' : w = (a ++ x :: (b ++ x :: (c ++ x :: (d ++ [x])))) ++ e := by simp [eq,append_assoc]
  have right := projected_bound low (back he (eq' ▸ cover))
  simp only [project_cons_self,project_append,project_free ha,project_free hb,project_free hc,
    project_free hd,length_append,show project x [x] = [] by simp [project],length_nil] at right
  have h₁ := projectedCut hb (l := a ++ [x]) (r := x :: (c ++ x :: (d ++ x :: e)))
    (x := x) (by simpa only [append_assoc,singleton_append] using eq ▸ cover)
  have h₂ := projectedCut hd (l := a ++ x :: (b ++ x :: (c ++ [x]))) (r := x :: e)
    (x := x) (by simpa [append_assoc] using eq ▸ cover)
  have emp : project x [x] = [] := by simp [project]
  simp only [project_append,project_cons_self,project_free ha,project_free hb,project_free hc,
    project_free hd,project_free he,emp,append_nil] at h₁ h₂
  have fifty₁ := outerCutLength nd nine (by omega : a.length ≤ 12) h₁ f2 f3 f6 f7 f8
  have fifty₂ := outerCutLength nd nine (by omega : e.length ≤ 12) (compatible_swap h₂) f2 f3 f6 f7 f8
  simp only [length_append] at fifty₁ fifty₂
  have gap := bridge (x := x) hc (alphabet := A)
    (fun i ne => (mem_erase_of_ne ne).mpr (mem_finRange i))
    (l := a ++ x :: (b ++ [x])) (r := x :: (d ++ x :: e))
    (by simpa [append_assoc] using eq ▸ cover)
  have lower := projected_bound low gap
  have hA : x ∉ A := (nodup_finRange 10).not_mem_erase
  simp only [project_append,project_cons_self,project_free ha,project_free hb,
    project_free hd,project_free he,project_free hA,emp,append_nil,length_append,nine] at lower
  omega
end Supersequence
