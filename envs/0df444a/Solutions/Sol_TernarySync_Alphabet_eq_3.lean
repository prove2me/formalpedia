-- Prove2me | solution 1 for TernarySync.Alphabet.eq_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:13.300274+00:00
-- url     : https://prove2.me/submissions/e57890cd-ec4c-43b8-a86c-43e4a9793b7e

import Mathlib
import Definitions.Def_TernarySync_Alphabet_EditDistance

section
set_option autoImplicit false

namespace TernarySync.Dev.Eq3
open TernarySync.Alphabet

theorem script_trans {α : Type*} {n m : ℕ} {x y z : List α}
    (h1 : IDScript n x y) (h2 : IDScript m y z) : IDScript (n + m) x z := by
  induction h1 with
  | refl x => simpa using h2
  | @step n' _ _ _ hs _ ih =>
    have := IDScript.step hs (ih h2)
    rwa [show n' + 1 + m = n' + m + 1 by omega]

theorem step_symm {α : Type*} {x y : List α} (h : IDStep x y) : IDStep y x := by
  rcases h with ⟨u, v, a, h1, h2⟩ | ⟨u, v, a, h1, h2⟩
  · exact Or.inr ⟨u, v, a, h2, h1⟩
  · exact Or.inl ⟨u, v, a, h2, h1⟩

theorem script_symm {α : Type*} {n : ℕ} {x y : List α} (h : IDScript n x y) :
    IDScript n y x := by
  induction h with
  | refl x => exact IDScript.refl x
  | step hs _ ih =>
    have := script_trans ih (IDScript.step (step_symm hs) (IDScript.refl _))
    simpa using this

theorem script_cons {α : Type*} {n : ℕ} {x y : List α} (a : α) (h : IDScript n x y) :
    IDScript n (a :: x) (a :: y) := by
  induction h with
  | refl x => exact IDScript.refl _
  | step hs _ ih =>
    refine IDScript.step ?_ ih
    rcases hs with ⟨u, v, b, h1, h2⟩ | ⟨u, v, b, h1, h2⟩
    · exact Or.inl ⟨a :: u, v, b, by simp [h1], by simp [h2]⟩
    · exact Or.inr ⟨a :: u, v, b, by simp [h1], by simp [h2]⟩

theorem script_of_sublist {α : Type*} {w x : List α} (h : w.Sublist x) :
    IDScript (x.length - w.length) x w := by
  induction h with
  | slnil => exact IDScript.refl _
  | cons a h ih =>
    rename_i l1 l2
    have hl := h.length_le
    have := IDScript.step (n := l2.length - l1.length) (x := a :: l2) (y := l2) (z := l1)
      (Or.inr ⟨[], l2, a, by simp, by simp⟩) ih
    simpa [show l2.length + 1 - l1.length = l2.length - l1.length + 1 by omega] using this
  | cons_cons a h ih =>
    simpa using script_cons a ih

theorem script_of_common {α : Type*} {w x y : List α} (hx : w.Sublist x) (hy : w.Sublist y) :
    IDScript ((x.length - w.length) + (y.length - w.length)) x y :=
  script_trans (script_of_sublist hx) (script_symm (script_of_sublist hy))

theorem lcs_set_bdd {α : Type*} (x y : List α) :
    BddAbove {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k} :=
  ⟨x.length, by rintro k ⟨z, hz, -, rfl⟩; exact hz.length_le⟩

theorem le_lcs {α : Type*} {w x y : List α} (hx : w.Sublist x) (hy : w.Sublist y) :
    w.length ≤ lcs x y :=
  le_csSup (lcs_set_bdd x y) ⟨w, hx, hy, rfl⟩

theorem lcs_attained {α : Type*} (x y : List α) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = lcs x y :=
  Nat.sSup_mem (s := {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k})
    ⟨0, [], by simp, by simp, rfl⟩ (lcs_set_bdd x y)

theorem lcs_le_left {α : Type*} (x y : List α) : lcs x y ≤ x.length := by
  obtain ⟨z, hz, -, h⟩ := lcs_attained x y
  rw [← h]; exact hz.length_le

theorem lcs_self {α : Type*} (x : List α) : lcs x x = x.length :=
  le_antisymm (lcs_le_left x x) (le_lcs (List.Sublist.refl x) (List.Sublist.refl x))

theorem lcs_mono {α : Type*} {x' x : List α} (z : List α) (h : x'.Sublist x) :
    lcs x' z ≤ lcs x z := by
  obtain ⟨w, hw1, hw2, hw⟩ := lcs_attained x' z
  rw [← hw]; exact le_lcs (hw1.trans h) hw2

theorem sub_erase {α : Type*} (a : α) (u v w : List α) (h : w.Sublist (u ++ a :: v)) :
    ∃ w' : List α, w'.Sublist (u ++ v) ∧ w'.Sublist w ∧ w.length ≤ w'.length + 1 := by
  induction u generalizing w with
  | nil =>
    simp only [List.nil_append] at h ⊢
    rcases List.sublist_cons_iff.1 h with hh | ⟨r, rfl, hh⟩
    · exact ⟨w, hh, List.Sublist.refl _, by omega⟩
    · exact ⟨r, hh, List.Sublist.cons _ (List.Sublist.refl _), by simp⟩
  | cons b u ih =>
    rcases List.sublist_cons_iff.1 h with hh | ⟨r, rfl, hh⟩
    · obtain ⟨w', h1, h2, h3⟩ := ih w hh
      exact ⟨w', h1.cons _, h2, h3⟩
    · obtain ⟨w', h1, h2, h3⟩ := ih r hh
      exact ⟨b :: w', h1.cons_cons _, h2.cons_cons _, by simp; omega⟩

theorem lcs_erase {α : Type*} (a : α) (u v z : List α) :
    lcs (u ++ a :: v) z ≤ lcs (u ++ v) z + 1 := by
  obtain ⟨w, hw1, hw2, hw⟩ := lcs_attained (u ++ a :: v) z
  obtain ⟨w', h1, h2, h3⟩ := sub_erase a u v w hw1
  have := le_lcs h1 (h2.trans hw2)
  omega

theorem lower {α : Type*} {n : ℕ} {x z : List α} (h : IDScript n x z) :
    (x.length : ℤ) + z.length - 2 * (lcs x z : ℤ) ≤ n := by
  induction h with
  | refl x => rw [lcs_self]; omega
  | @step n' x' y' z' hs _ ih =>
    rcases hs with ⟨u, v, a, h1, h2⟩ | ⟨u, v, a, h1, h2⟩
    · subst h1 h2
      have := lcs_erase a u v z'
      simp at *; omega
    · subst h1 h2
      have := lcs_mono z' (show (u ++ v).Sublist (u ++ a :: v) from
        (List.Sublist.refl u).append (List.Sublist.cons _ (List.Sublist.refl v)))
      simp at *; omega

end TernarySync.Dev.Eq3

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq3 in
theorem chk_eq_3 {α : Type*} (x y : List α) :
    (ed x y : ℤ) = (x.length : ℤ) + (y.length : ℤ) - 2 * (lcs x y : ℤ) := by
  obtain ⟨w, hw1, hw2, hw⟩ := lcs_attained x y
  have hne : {n : ℕ | IDScript n x y}.Nonempty := ⟨_, script_of_common hw1 hw2⟩
  have hle : ed x y ≤ (x.length - w.length) + (y.length - w.length) :=
    Nat.sInf_le (script_of_common hw1 hw2)
  have hmem : IDScript (ed x y) x y := Nat.sInf_mem hne
  have h1 := lower hmem
  have := hw1.length_le
  have := hw2.length_le
  omega
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_3 := @TernarySync.Alphabet.chk_eq_3
