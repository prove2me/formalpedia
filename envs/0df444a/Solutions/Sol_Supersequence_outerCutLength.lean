-- Prove2me | solution 1 for Supersequence.outerCutLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:00.926819+00:00
-- url     : https://prove2.me/submissions/e3d2f98a-57d4-4b26-a51b-423d28a7cd24

import Definitions.Def_Frequency
import Definitions.Def_Four
import Theorems.Thm_Supersequence_heavyLetter
import Theorems.Thm_Supersequence_project_append
import Theorems.Thm_Supersequence_project_cons_self
import Theorems.Thm_Supersequence_universal_iff_covers
attribute [local simp] Supersequence.project_append
attribute [local simp] Supersequence.project_cons_self


section
namespace Supersequence
open List
variable {α : Type} [DecidableEq α]
private theorem mass_cons (a : α) (w A : List α) :
    mass (a::w) A = mass w A + A.count a := by
  induction A with
  | nil => simp [mass]
  | cons b A ih =>
    by_cases e : a=b
    · subst b; simp [mass,count_cons] at *; omega
    · simp [mass,count_cons,e,Ne.symm e] at *; omega
private theorem mass_eq {A : List α} (nd : A.Nodup) (w : List α) :
    mass w A = (w.filter A.contains).length := by
  induction w with
  | nil => induction A <;> simp_all [mass]
  | cons a w ih =>
    rw [mass_cons, ih, nd.count]
    by_cases ha : a ∈ A <;> simp [ha]
private theorem mass_le (w : List α) {A : List α} (nd : A.Nodup) :
    mass w A ≤ w.length := by rw [mass_eq nd]; apply length_filter_le
private theorem mass_split {A S : List α} (ha : A.Nodup) (hs : S.Nodup) (sub : S ⊆ A) :
    (S ++ rest A S).Perm A := by
  have nd : (S ++ rest A S).Nodup := by
    refine nodup_append.mpr ⟨hs,ha.sublist filter_sublist,?_⟩
    intro a h b hb e
    simp [rest,←e,h] at hb
  apply perm_iff_count.mpr
  intro a
  rw [nd.count,ha.count]
  by_cases h : a ∈ S
  · simp [rest,h,sub h]
  · simp [rest,h]
private theorem facts {A S : List α} (ha : A.Nodup) (hs : S.Nodup) (sub : S ⊆ A) (w : List α) :
    S.length + (rest A S).length = A.length ∧ mass w S + mass w (rest A S) = mass w A := by
  have hp := mass_split ha hs sub
  refine ⟨by simpa using hp.length_eq, ?_⟩
  have eq : mass w (S ++ rest A S) = mass w A := by
    rw [mass_eq (hp.nodup_iff.mpr ha), mass_eq ha]
    congr 1
    apply filter_congr
    intro a _
    simp [hp.mem_iff]
  simpa [mass] using eq
private theorem mass_upper {w A : List α} {c : Nat} (h : ∀ a ∈ A, w.count a ≤ c) :
    mass w A ≤ A.length*c := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    have ht := ih (fun b hb => h b (.tail _ hb))
    have hh := h a (.head _)
    simp [mass,Nat.succ_mul] at *; omega
private theorem mass_lower {w A : List α} {c : Nat} (h : ∀ a ∈ A, c ≤ w.count a) :
    A.length*c ≤ mass w A := by
  induction A with
  | nil => simp [mass]
  | cons a A ih =>
    have ht := ih (fun b hb => h b (.tail _ hb))
    have hh := h a (.head _)
    simp [mass,Nat.succ_mul] at *; omega
private theorem on_subset {A w : List α} {k L : Nat} (bound : LengthBound k L)
    (hn : A.Nodup) (len : A.length = k) (hk : 0 < k) (cov : Covers (· ∈ A) w) :
    L ≤ mass w A := by
  subst k
  let enc (i : Fin A.length) := A.get i
  let dec (a : α) : Fin A.length := ⟨A.idxOf a % A.length,Nat.mod_lt _ hk⟩
  have inv (i : Fin A.length) : dec (enc i) = i := by
    apply Fin.ext; simp [dec,enc,hn.idxOf_getElem i.val i.isLt,Nat.mod_eq_of_lt i.isLt]
  let old := w.filter A.contains
  have hc : Covers (fun _ => True) (old.map dec) := by
    intro q hq _
    have nd : (q.map enc).Nodup := pairwise_map.mpr (hq.imp (by
      intro a b hab e; exact hab (by simpa only [inv] using congrArg dec e)))
    have mem : ∀ a ∈ q.map enc, a ∈ A := by
      intro a ha; obtain ⟨i,_,rfl⟩ := mem_map.mp ha; exact A.get_mem i
    have he := (cov _ nd mem).filter A.contains
    rw [filter_eq_self.mpr (by simpa using mem)] at he
    have result := he.map dec
    simpa [map_map,Function.comp_def,inv,old] using result
  rw [mass_eq hn]
  simpa [old] using bound _ (universal_iff_covers.mpr hc)
omit [DecidableEq α] in
private theorem mono {P Q : α → Prop} {w : List α} (h : Covers P w)
    (sub : ∀ a, Q a → P a) : Covers Q w :=
  fun r hn mem => h r hn (fun a ha => sub a (mem a ha))
private theorem positiveSide {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (cutOK : Compatible A p q) (f8 : LengthBound 8 52) (short : q.length < 52) :
    ∀ a ∈ A, a ∈ p := by
  have totalQ := mass_le q ha
  intro a mem
  apply Classical.byContradiction; intro missing
  have sub : [a] ⊆ A := by simpa using mem
  rcases cutOK [a] sub with left | right
  · exact missing (singleton_sublist.mp (left [a] (by simp) (by simp)))
  · obtain ⟨len,eq⟩ := facts ha (by simp : [a].Nodup) sub q
    have h := on_subset f8 (ha.sublist filter_sublist)
      (A := rest A [a]) (by simp at len; omega) (by decide) right
    omega
private theorem supply {A p : List α} (ha : A.Nodup) (n : A.length = 9)
    (all : ∀ a ∈ A, a ∈ p) : 18 ≤ p.length + (onesIn p A).length := by
  have totalP := mass_le p ha
  let singles := A.filter (fun a => p.count a == 1)
  have ns : singles.Nodup := ha.sublist filter_sublist
  have subS : singles ⊆ A := filter_sublist.subset
  have single (a) (h : a ∈ singles) : p.count a = 1 := by simpa [singles] using (mem_filter.mp h).2
  change 18 ≤ p.length + singles.length
  obtain ⟨len,eq⟩ := facts ha ns subS p
  have ones := mass_lower (c := 1) (A := singles) (w := p) (by grind)
  have twos := mass_lower (c := 2) (A := rest A singles) (w := p) (by
    intro a mem
    have ⟨aa,notin⟩ := mem_filter.mp mem
    have pos := count_pos_iff.mpr (all a aa)
    have neq : p.count a ≠ 1 := by
      intro one; have ins : a ∈ singles := by simp [singles,aa,one]
      simp [ins] at notin
    omega)
  omega
private theorem coverSix {A p q S : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 12) (cutOK : Compatible A p q) (f3 : LengthBound 3 7)
    (ndS : S.Nodup) (lenS : S.length = 6) (subSA : S ⊆ A)
    (ones : ∀ a ∈ S, p.count a = 1) : Covers (· ∈ S) q := by
  have totalP := mass_le p ha
  have bounds := facts ha ndS subSA p
  have comp3 : (rest A S).length = 3 := by omega
  have compSub : rest A S ⊆ A := filter_sublist.subset
  rcases cutOK (rest A S) compSub with left | right
  · have three := on_subset f3 (ha.sublist filter_sublist) comp3 (by decide) left
    change 7 ≤ mass p (rest A S) at three
    have six := mass_lower (w := p) (A := S) (c := 1) (by grind)
    omega
  · apply mono right
    intro a mem
    simp [rest,mem,subSA mem]
private theorem pairBudget {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (cutOK : Compatible A p q) (f2 : LengthBound 2 3) (f7 : LengthBound 7 39)
    {a b : α} (aa : a ∈ A) (bb : b ∈ A) (ne : a ≠ b)
    (oneA : p.count a = 1) (oneB : p.count b = 1) : q.count a + q.count b + 39 ≤ q.length := by
  have totalQ := mass_le q ha
  have nd : [a,b].Nodup := by simp [ne]
  have sub : [a,b] ⊆ A := by simpa using And.intro aa bb
  obtain ⟨len,eq⟩ := facts ha nd sub q
  rcases cutOK [a,b] sub with left | right
  · have h := on_subset f2 nd rfl (by decide) left
    simp [mass,oneA,oneB] at h
  · have h := on_subset f7 (ha.sublist filter_sublist) (A := rest A [a,b])
        (by simp at len; omega) (by decide) right
    simp [mass] at eq totalQ
    change 39 ≤ (map (fun z => q.count z) (rest A [a,b])).sum at h
    omega
end Supersequence
end

set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]
namespace Supersequence
theorem _root_.solution {A p q : List α} (ha : A.Nodup) (n : A.length = 9)
    (small : p.length ≤ 12) (cutOK : Compatible A p q)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) : 50 ≤ q.length := by
  apply Classical.byContradiction
  intro short
  have all := positiveSide ha n cutOK f8 (by omega)
  let singles := onesIn p A
  have ns : singles.Nodup := ha.sublist filter_sublist
  have subS : singles ⊆ A := filter_sublist.subset
  have single (a) (h : a ∈ singles) : p.count a = 1 := by simpa [singles,onesIn] using (mem_filter.mp h).2
  have enough : 6 ≤ singles.length := by have := supply ha n all; change 6 ≤ (onesIn p A).length; omega
  let S := singles.take 6
  have lenS : S.length = 6 := by simp [S,length_take,Nat.min_eq_left enough]
  have ndS : S.Nodup := ns.sublist (take_sublist ..)
  have subSA : S ⊆ A := fun _ h => subS (mem_of_mem_take h)
  have ones (a) (h : a ∈ S) := single a (mem_of_mem_take h)
  have covered := coverSix ha n small cutOK f3 ndS lenS subSA ones
  have twentyEight := on_subset f6 ndS lenS (by decide) covered
  obtain ⟨a,haS,heavy⟩ := heavyLetter ndS (by intro e; simp [e] at lenS) covered
  let R := rest S [a]
  have pairbound (b : α) (hb : b ∈ R) : q.count a + q.count b ≤ 10 := by
    have ⟨hbS,neq⟩ := mem_filter.mp hb
    have ne : a ≠ b := by intro e; simp [← e] at neq
    have := pairBudget ha n cutOK f2 f7 (subSA haS) (subSA hbS) ne (ones a haS) (ones b hbS)
    omega
  obtain ⟨lenR,eqR⟩ := facts ndS (by simp : [a].Nodup) (by simpa using haS : [a] ⊆ S) q
  have five : R.length = 5 := by change 1 + R.length = S.length at lenR; omega
  have someR : ∃ b, b ∈ R := by cases e : R with
                                  | nil => simp [e] at five
                                  | cons b t => exact ⟨b,by simp⟩
  obtain ⟨b,hb⟩ := someR
  have lim := pairbound b hb
  have sum := mass_upper (A := R) (w := q) (c := 10 - q.count a)
    (by intro c hc; have := pairbound c hc; omega)
  change mass q [a] + mass q R = mass q S at eqR
  rw [show mass q [a] = q.count a by simp [mass]] at eqR
  rw [five] at sum
  omega
end Supersequence
