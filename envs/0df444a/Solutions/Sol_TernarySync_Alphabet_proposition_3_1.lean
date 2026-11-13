-- Prove2me | solution 1 for TernarySync.Alphabet.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:15:37.23824+00:00
-- url     : https://prove2.me/submissions/4cd7f90f-2514-4553-97d6-ef2bad69ed84

import Mathlib
import Definitions.Def_TernarySync_Alphabet_Brinkhuis

section
set_option autoImplicit false

namespace TernarySync.Dev.Prop31
open TernarySync.Alphabet

def eqN : List (Fin 3) → List (Fin 3) → ℕ → Bool
  | _, _, 0 => true
  | x :: xs, y :: ys, n + 1 => x == y && eqN xs ys n
  | _, _, _ => false

theorem eqN_of {n : ℕ} : ∀ {u v : List (Fin 3)}, n ≤ u.length → n ≤ v.length →
    (∀ i < n, u.getD i 0 = v.getD i 0) → eqN u v n = true := by
  induction n with
  | zero => intro u v _ _ _; cases u <;> cases v <;> simp [eqN]
  | succ n ih =>
    intro u v hu hv h
    match u, v, hu, hv with
    | x :: xs, y :: ys, hu, hv =>
      simp only [eqN, Bool.and_eq_true, beq_iff_eq]
      refine ⟨by simpa using h 0 (by omega), ih (by simpa using hu) (by simpa using hv) ?_⟩
      intro i hi
      simpa using h (i + 1) (by omega)

def sqB (S : List (Fin 3)) : Bool :=
  (List.range S.length).all fun s =>
    (List.range ((S.drop s).length / 2 + 1)).all fun p =>
      p == 0 || !(eqN (S.drop s) ((S.drop s).drop p) p)

theorem getD_drop' (S : List (Fin 3)) (s i : ℕ) : (S.drop s).getD i 0 = S.getD (s + i) 0 := by
  by_cases h : s + i < S.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem sqB_sound (S : List (Fin 3)) (h : sqB S = true) :
    ∀ s p, 0 < p → s + 2 * p ≤ S.length →
      ∃ i < p, S.getD (s + i) 0 ≠ S.getD (s + p + i) 0 := by
  intro s p hp hs
  unfold sqB at h
  rw [List.all_eq_true] at h
  have h1 := h s (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h1
  have h2 := h1 p (List.mem_range.2 (by simp; omega))
  by_contra hc
  push Not at hc
  have : eqN (S.drop s) ((S.drop s).drop p) p = true := by
    apply eqN_of (by simp; omega) (by simp; omega)
    intro i hi
    rw [getD_drop', getD_drop', getD_drop', show s + (p + i) = s + p + i by omega]
    exact hc i hi
  rw [this] at h2
  simp at h2
  omega

def tab : List (List (List (Fin 3))) :=
  [[[2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2], [2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2]],
   [[0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0], [0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0]],
   [[1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1], [1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1]]]

def cw (a : Fin 3) (r : Fin 2) : List (Fin 3) := ((tab.getD a.val []).getD r.val [])

theorem cw_eq : ∀ a r, codeword a r = cw a r := by decide

theorem big_check :
    ∀ a b c : Fin 3, a ≠ b → b ≠ c → ∀ r t u : Fin 2,
      sqB (cw a r ++ cw b t ++ cw c u) = true := by
  decide +kernel

def items : List (Fin 3 × Fin 3 × Fin 2 × Fin 2 × ℕ) :=
  (List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
    if a = b then [] else (List.finRange 2).flatMap fun r => (List.finRange 2).flatMap fun t =>
      (List.range 18).map fun o => (a, b, r, t, o)

def tblLit : List (List ℕ × ℕ) :=
  [([2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0], 0),
   ([1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2], 1),
   ([0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0], 2),
   ([2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1], 3),
   ([0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2], 4),
   ([1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0], 5),
   ([2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2], 6),
   ([0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1], 7),
   ([2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0], 8),
   ([1, 2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1], 9),
   ([2, 0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2], 10),
   ([0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0], 11),
   ([1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1], 12),
   ([0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0], 13),
   ([2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2], 14),
   ([0, 1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0], 15),
   ([1, 2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1], 16),
   ([2, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2], 17),
   ([0, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 1], 11),
   ([1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0], 12),
   ([0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2], 13),
   ([2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0], 14),
   ([0, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1], 15),
   ([1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0], 16),
   ([2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2], 17),
   ([2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0], 0),
   ([1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2], 1),
   ([0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0], 2),
   ([2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1], 3),
   ([0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2], 4),
   ([1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0], 5),
   ([0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2], 6),
   ([2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1], 7),
   ([1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0], 8),
   ([2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1], 9),
   ([0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2], 10),
   ([2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 0], 11),
   ([2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 1, 2, 1], 11),
   ([1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1], 5),
   ([2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0], 6),
   ([0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2], 7),
   ([2, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1], 8),
   ([1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2], 9),
   ([2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0], 10),
   ([0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1], 11),
   ([1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2], 12),
   ([0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1], 13),
   ([2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0], 14),
   ([0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1], 15),
   ([1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2], 16),
   ([2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0], 17),
   ([0, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 2], 11),
   ([1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 2, 1], 12),
   ([0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 2, 1, 0], 13),
   ([2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1], 14),
   ([0, 1, 2, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2], 15),
   ([1, 2, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1], 16),
   ([2, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0], 17),
   ([1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1], 5),
   ([0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0], 6),
   ([2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2], 7),
   ([1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1], 8),
   ([2, 0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2], 9),
   ([0, 2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0], 10),
   ([2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1], 11),
   ([2, 1, 0, 2, 0, 1, 2, 1, 0, 2, 1, 2, 0, 2], 11),
   ([0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1], 0),
   ([2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0], 1),
   ([1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1], 2),
   ([0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2], 3),
   ([1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0], 4),
   ([2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2], 5),
   ([0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1], 6),
   ([1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 0], 7),
   ([0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2], 8),
   ([2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0], 9),
   ([0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1], 10),
   ([1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2], 11),
   ([2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0], 12),
   ([1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2], 13),
   ([0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1], 14),
   ([1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2], 15),
   ([2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0], 16),
   ([0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1], 17),
   ([1, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0], 11),
   ([2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2], 12),
   ([1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1], 13),
   ([0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2], 14),
   ([1, 2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0], 15),
   ([2, 0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2], 16),
   ([0, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1], 17),
   ([0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1], 0),
   ([2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0], 1),
   ([1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1], 2),
   ([0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2], 3),
   ([1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0], 4),
   ([2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 2], 5),
   ([1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 2, 1], 6),
   ([0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0], 7),
   ([2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2], 8),
   ([0, 1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0], 9),
   ([1, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1], 10),
   ([0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2], 11),
   ([0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 0], 11),
   ([2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 1], 5),
   ([0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 1, 0], 6),
   ([1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 1, 0, 2], 7),
   ([0, 2, 0, 1, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1], 8),
   ([2, 0, 1, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2], 9),
   ([0, 1, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0], 10),
   ([1, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1], 11),
   ([2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2], 12),
   ([1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1], 13),
   ([0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0], 14),
   ([1, 2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1], 15),
   ([2, 0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2], 16),
   ([0, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0], 17),
   ([1, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2], 11),
   ([2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1], 12),
   ([1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0], 13),
   ([0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1], 14),
   ([1, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2], 15),
   ([2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1], 16),
   ([0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0], 17),
   ([2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1], 5),
   ([1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0], 6),
   ([0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2], 7),
   ([2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1], 8),
   ([0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2], 9),
   ([1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0], 10),
   ([0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 1], 11),
   ([0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 1, 2, 0, 2], 11),
   ([1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2], 0),
   ([0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1], 1),
   ([2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2], 2),
   ([1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0], 3),
   ([2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1], 4),
   ([0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 2], 5),
   ([1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 2, 1], 6),
   ([2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 2, 1, 0], 7),
   ([1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2], 8),
   ([0, 1, 2, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0], 9),
   ([1, 2, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1], 10),
   ([2, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2], 11),
   ([0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0], 12),
   ([2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 2], 13),
   ([1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1], 14),
   ([2, 0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2], 15),
   ([0, 1, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0], 16),
   ([1, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1], 17),
   ([2, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0], 11),
   ([0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2], 12),
   ([2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1], 13),
   ([1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2], 14),
   ([2, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0], 15),
   ([0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2], 16),
   ([1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1], 17),
   ([1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2], 0),
   ([0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1], 1),
   ([2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2], 2),
   ([1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0], 3),
   ([2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1], 4),
   ([0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2], 5),
   ([2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1], 6),
   ([1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0], 7),
   ([0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2], 8),
   ([1, 2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0], 9),
   ([2, 1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1], 10),
   ([1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 2], 11),
   ([1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 2, 0, 1, 0], 11),
   ([0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0], 5),
   ([1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2], 6),
   ([2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 1], 7),
   ([1, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0], 8),
   ([0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1], 9),
   ([1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2], 10),
   ([2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0], 11),
   ([0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1], 12),
   ([2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0], 13),
   ([1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2], 14),
   ([2, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0], 15),
   ([0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1], 16),
   ([1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2], 17),
   ([2, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 1], 11),
   ([0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0], 12),
   ([2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2], 13),
   ([1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0], 14),
   ([2, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1], 15),
   ([0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0], 16),
   ([1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2], 17),
   ([0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 0], 5),
   ([2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 0, 2], 6),
   ([1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1], 7),
   ([0, 1, 2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0], 8),
   ([1, 2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1], 9),
   ([2, 1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2], 10),
   ([1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0], 11),
   ([1, 0, 2, 1, 2, 0, 1, 0, 2, 1, 0, 1, 2, 1], 11)]

def winOf (x : Fin 3 × Fin 3 × Fin 2 × Fin 2 × ℕ) : List ℕ :=
  (List.range 14).map fun j => ((cw x.1 x.2.2.1 ++ cw x.2.1 x.2.2.2.1).getD (x.2.2.2.2 + j) 0).val

theorem tbl_complete : ∀ x ∈ items, (winOf x, x.2.2.2.2) ∈ tblLit := by decide +kernel

theorem tbl_unique : ∀ x ∈ tblLit, ∀ y ∈ tblLit, x.1 = y.1 → x.2 = y.2 := by decide +kernel

theorem mem_items (a b : Fin 3) (r t : Fin 2) (o : ℕ) (hab : a ≠ b) (ho : o < 18) :
    (a, b, r, t, o) ∈ items := by
  simp [items, hab, ho]

theorem sync_check (a b : Fin 3) (hab : a ≠ b) (r t : Fin 2) (a' b' : Fin 3) (hab' : a' ≠ b')
    (r' t' : Fin 2) (o : ℕ) (ho : o < 18) (o' : ℕ) (ho' : o' < 18)
    (h : ∀ j < 14, (codeword a r ++ codeword b t).getD (o + j) 0
          = (codeword a' r' ++ codeword b' t').getD (o' + j) 0) : o = o' := by
  have h1 := tbl_complete _ (mem_items a b r t o hab ho)
  have h2 := tbl_complete _ (mem_items a' b' r' t' o' hab' ho')
  have hw : winOf (a, b, r, t, o) = winOf (a', b', r', t', o') := by
    unfold winOf
    apply List.map_congr_left
    intro j hj
    simp only [List.mem_range] at hj
    have := h j hj
    simp only [cw_eq] at this
    exact congrArg Fin.val this
  exact tbl_unique _ h1 _ h2 hw

/-- A block of the substitution: the pair `(a, r)` is sent to `B_{a,r}`. -/
def blk (x : Fin 3 × Fin 2) : List (Fin 3) := codeword x.1 x.2

/-- Substitution on lists of (letter, choice) pairs. -/
def WP (Ps : List (Fin 3 × Fin 2)) : List (Fin 3) := (Ps.map blk).flatten

theorem len_check : ∀ a : Fin 3, ∀ r : Fin 2, (codeword a r).length = 18 := by decide

theorem blk_length (x : Fin 3 × Fin 2) : (blk x).length = 18 := len_check x.1 x.2

theorem WP_nil : WP [] = [] := rfl

theorem WP_cons (x : Fin 3 × Fin 2) (Ps : List (Fin 3 × Fin 2)) :
    WP (x :: Ps) = blk x ++ WP Ps := by simp [WP]

theorem WP_append (Ps Qs : List (Fin 3 × Fin 2)) : WP (Ps ++ Qs) = WP Ps ++ WP Qs := by
  simp [WP]

theorem WP_length (Ps : List (Fin 3 × Fin 2)) : (WP Ps).length = 18 * Ps.length := by
  induction Ps with
  | nil => rfl
  | cons x Ps ih => rw [WP_cons, List.length_append, blk_length, ih, List.length_cons]; ring

theorem WP_getD_drop (Ps : List (Fin 3 × Fin 2)) (k : ℕ) (hk : k ≤ Ps.length) (x : ℕ) :
    (WP Ps).getD (18 * k + x) 0 = (WP (Ps.drop k)).getD x 0 := by
  conv_lhs => rw [← List.take_append_drop k Ps, WP_append]
  have hl : (WP (Ps.take k)).length = 18 * k := by
    rw [WP_length, List.length_take]; congr 1; omega
  rw [List.getD_append_right _ _ _ _ (by omega), hl]
  congr 1; omega

theorem WP_getD_block (Ps : List (Fin 3 × Fin 2)) (k : ℕ) (hk : k < Ps.length) (x : ℕ)
    (hx : x < 18) :
    (WP Ps).getD (18 * k + x) 0 = (blk (Ps.getD k (0, 0))).getD x 0 := by
  rw [WP_getD_drop Ps k hk.le, List.drop_eq_getElem_cons hk, WP_cons,
    List.getD_append _ _ _ _ (by rw [blk_length]; exact hx), List.getD_eq_getElem _ _ hk]

theorem getD_trunc (A B C : List (Fin 3)) (x : ℕ) (hx : x < (A ++ B).length) :
    (A ++ B ++ C).getD x 0 = (A ++ B).getD x 0 := List.getD_append _ _ _ _ hx

theorem succ_ne : ∀ z : Fin 3, z ≠ z + 1 := by decide
theorem succ_ne2 : ∀ z : Fin 3, z + 1 ≠ z + 2 := by decide

theorem blocks3 (Ps : List (Fin 3 × Fin 2))
    (hch : ∀ i, i + 1 < Ps.length → (Ps.getD i (0, 0)).1 ≠ (Ps.getD (i + 1) (0, 0)).1)
    (k : ℕ) (hk : k < Ps.length) :
    ∃ b c : Fin 3 × Fin 2, (Ps.getD k (0, 0)).1 ≠ b.1 ∧ b.1 ≠ c.1 ∧
      ∀ x, x < 54 → 18 * k + x < 18 * Ps.length →
        (WP Ps).getD (18 * k + x) 0 = (blk (Ps.getD k (0, 0)) ++ blk b ++ blk c).getD x 0 := by
  have hd := List.drop_eq_getElem_cons hk
  rw [← List.getD_eq_getElem Ps (0, 0) hk] at hd
  by_cases h2 : k + 2 < Ps.length
  · have hd1 := List.drop_eq_getElem_cons (show k + 1 < Ps.length by omega)
    have hd2 := List.drop_eq_getElem_cons h2
    rw [← List.getD_eq_getElem Ps (0, 0) (show k + 1 < Ps.length by omega)] at hd1
    rw [← List.getD_eq_getElem Ps (0, 0) h2] at hd2
    refine ⟨Ps.getD (k + 1) (0, 0), Ps.getD (k + 2) (0, 0), hch k (by omega),
      hch (k + 1) (by omega), ?_⟩
    intro x hx _
    rw [WP_getD_drop Ps k hk.le, hd, hd1, hd2]
    simp only [WP_cons]
    rw [← List.append_assoc, ← List.append_assoc]
    rw [List.getD_append _ _ _ _ (by simp [blk_length]; omega)]
  · by_cases h1 : k + 1 < Ps.length
    · have hd1 := List.drop_eq_getElem_cons h1
      rw [← List.getD_eq_getElem Ps (0, 0) h1] at hd1
      have hd2 : Ps.drop (k + 2) = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨Ps.getD (k + 1) (0, 0), ((Ps.getD (k + 1) (0, 0)).1 + 1, 0), hch k h1, ?_, ?_⟩
      · exact succ_ne _
      · intro x hx hx2
        rw [WP_getD_drop Ps k hk.le, hd, hd1, hd2]
        simp only [WP_cons, WP_nil, List.append_nil]
        exact (getD_trunc _ _ _ _ (by simp [blk_length]; omega)).symm
    · have hd1 : Ps.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
      refine ⟨((Ps.getD k (0, 0)).1 + 1, 0), ((Ps.getD k (0, 0)).1 + 2, 0), ?_, ?_, ?_⟩
      · exact succ_ne _
      · exact succ_ne2 _
      · intro x hx hx2
        rw [WP_getD_drop Ps k hk.le, hd, hd1]
        simp only [WP_cons, WP_nil, List.append_nil]
        have hx18 : x < 18 := by omega
        rw [getD_trunc _ _ _ _ (by simp [blk_length]; omega),
          List.getD_append _ _ _ _ (by simp [blk_length]; omega)]

/-- Index form of square-freeness. -/
theorem sqfree_iff (S : List (Fin 3)) :
    IsSquareFree S ↔ ∀ s p, 0 < p → s + 2 * p ≤ S.length →
      ∃ i < p, S.getD (s + i) 0 ≠ S.getD (s + p + i) 0 := by
  constructor
  · intro h s p hp hs
    by_contra hc
    push Not at hc
    apply h ((S.drop s).take (2 * p))
    · exact ((List.take_prefix _ _).isInfix).trans ((List.drop_suffix _ _).isInfix)
    · refine ⟨(S.drop s).take p, ?_, ?_⟩
      · intro h0
        have := congrArg List.length h0
        simp at this; omega
      · rw [two_mul, List.take_add, List.drop_drop]
        congr 1
        apply List.ext_getElem
        · simp; omega
        · intro i h1 h2
          have h3 : i < p := by simp at h1; omega
          have := hc i h3
          rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
          simp only [List.getElem_take, List.getElem_drop]
          rw [this]
  · intro h w hw ⟨X, hX, hwX⟩
    obtain ⟨pre, suf, hS⟩ := hw
    subst hwX
    have hXl : 0 < X.length := List.length_pos_iff.2 hX
    have hlen : S.length = pre.length + (X.length + X.length) + suf.length := by
      rw [← hS]; simp; omega
    obtain ⟨i, hi, hne⟩ := h pre.length X.length hXl (by omega)
    apply hne
    rw [← hS]
    have e1 : (pre ++ (X ++ X) ++ suf).getD (pre.length + i) 0 = X.getD i 0 := by
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega),
        show pre.length + i - pre.length = i by omega, List.getD_append _ _ _ _ hi]
    have e2 : (pre ++ (X ++ X) ++ suf).getD (pre.length + X.length + i) 0 = X.getD i 0 := by
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega),
        show pre.length + X.length + i - pre.length = X.length + i by omega,
        List.getD_append_right _ _ _ _ (by omega),
        show X.length + i - X.length = i by omega]
    rw [e1, e2]

theorem small_check :
    ∀ a b c : Fin 3, a ≠ b → b ≠ c → ∀ r t u : Fin 2, ∀ o < 18, ∀ p < 14, 0 < p →
      ∃ i < p, (codeword a r ++ codeword b t ++ codeword c u).getD (o + i) 0
        ≠ (codeword a r ++ codeword b t ++ codeword c u).getD (o + p + i) 0 := by
  decide +kernel

theorem first_check : ∀ a a' : Fin 3, ∀ r r' : Fin 2,
    (codeword a r).getD 0 0 = (codeword a' r').getD 0 0 → a = a' := by
  decide

theorem inj_check : ∀ a : Fin 3, ∀ r r' : Fin 2, codeword a r = codeword a r' → r = r' := by
  decide

theorem distinct_check : ∀ a : Fin 3, codeword a 0 ≠ codeword a 1 := by decide

theorem getD_map_fst (Ps : List (Fin 3 × Fin 2)) (i : ℕ) :
    (Ps.map Prod.fst).getD i 0 = (Ps.getD i (0, 0)).1 := by
  induction Ps generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ n => rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]; exact ih n

theorem main_sqfree (Ps : List (Fin 3 × Fin 2)) (hsf : IsSquareFree (Ps.map Prod.fst)) :
    IsSquareFree (WP Ps) := by
  have hsf' := (sqfree_iff _).1 hsf
  have hch : ∀ i, i + 1 < Ps.length → (Ps.getD i (0, 0)).1 ≠ (Ps.getD (i + 1) (0, 0)).1 := by
    intro i hi heq
    obtain ⟨j, hj, hne⟩ := hsf' i 1 (by omega) (by simpa using (by omega : i + 2 ≤ Ps.length))
    have hj0 : j = 0 := by omega
    subst hj0
    apply hne
    rw [getD_map_fst, getD_map_fst]; exact heq
  rw [sqfree_iff]
  intro s p hp hlen
  by_contra hcon
  push Not at hcon
  rw [WP_length] at hlen
  have hsl : s / 18 < Ps.length := by omega
  by_cases hp14 : p ≤ 13
  · obtain ⟨b, c, hab, hbc, hB⟩ := blocks3 Ps hch (s / 18) hsl
    obtain ⟨i, hi, hne⟩ := small_check _ _ _ hab hbc (Ps.getD (s / 18) (0, 0)).2 b.2 c.2
      (s % 18) (by omega) p (by omega) hp
    apply hne
    have h1 := hB (s % 18 + i) (by omega) (by omega)
    have h2 := hB (s % 18 + p + i) (by omega) (by omega)
    rw [show 18 * (s / 18) + (s % 18 + i) = s + i by omega] at h1
    rw [show 18 * (s / 18) + (s % 18 + p + i) = s + p + i by omega] at h2
    have := hcon i hi
    simp only [blk] at h1 h2
    rw [← h1, ← h2]; exact this
  · push Not at hp14
    have hsl2 : (s + p) / 18 < Ps.length := by omega
    obtain ⟨b, c, hab, hbc, hB⟩ := blocks3 Ps hch (s / 18) hsl
    obtain ⟨b', c', hab', hbc', hB'⟩ := blocks3 Ps hch ((s + p) / 18) hsl2
    have hsync := sync_check (Ps.getD (s / 18) (0, 0)).1 b.1 hab (Ps.getD (s / 18) (0, 0)).2 b.2
      (Ps.getD ((s + p) / 18) (0, 0)).1 b'.1 hab' (Ps.getD ((s + p) / 18) (0, 0)).2 b'.2
      (s % 18) (by omega) ((s + p) % 18) (by omega) (by
        intro j hj
        have h1 := hB (s % 18 + j) (by omega) (by omega)
        have h2 := hB' ((s + p) % 18 + j) (by omega) (by omega)
        rw [show 18 * (s / 18) + (s % 18 + j) = s + j by omega] at h1
        rw [show 18 * ((s + p) / 18) + ((s + p) % 18 + j) = s + p + j by omega] at h2
        have e1 : (codeword (Ps.getD (s / 18) (0, 0)).1 (Ps.getD (s / 18) (0, 0)).2
            ++ codeword b.1 b.2).getD (s % 18 + j) 0 = (WP Ps).getD (s + j) 0 := by
          rw [h1]; exact (getD_trunc _ _ _ _ (by simp [len_check]; omega)).symm
        have e2 : (codeword (Ps.getD ((s + p) / 18) (0, 0)).1 (Ps.getD ((s + p) / 18) (0, 0)).2
            ++ codeword b'.1 b'.2).getD ((s + p) % 18 + j) 0 = (WP Ps).getD (s + p + j) 0 := by
          rw [h2]; exact (getD_trunc _ _ _ _ (by simp [len_check]; omega)).symm
        rw [e1, e2]; exact hcon j (by omega))
    obtain ⟨q, hq⟩ : 18 ∣ p := by omega
    have hq1 : 0 < q := by omega
    have hT : ∀ i < q, (Ps.map Prod.fst).getD ((s + 17) / 18 + i) 0
        = (Ps.map Prod.fst).getD ((s + 17) / 18 + q + i) 0 := by
      intro i hi
      rw [getD_map_fst, getD_map_fst]
      have e := hcon (18 * ((s + 17) / 18 + i) - s) (by omega)
      rw [show s + (18 * ((s + 17) / 18 + i) - s) = 18 * ((s + 17) / 18 + i) + 0 by omega,
        show s + p + (18 * ((s + 17) / 18 + i) - s) = 18 * ((s + 17) / 18 + q + i) + 0 by omega,
        WP_getD_block Ps ((s + 17) / 18 + i) (by omega) 0 (by omega),
        WP_getD_block Ps ((s + 17) / 18 + q + i) (by omega) 0 (by omega)] at e
      exact first_check _ _ _ _ e
    obtain ⟨i, hi, hne⟩ := hsf' ((s + 17) / 18) q hq1 (by rw [List.length_map]; omega)
    exact hne (hT i hi)

theorem WP_inj (Ps Qs : List (Fin 3 × Fin 2)) (h : Ps.map Prod.fst = Qs.map Prod.fst)
    (hW : WP Ps = WP Qs) : Ps = Qs := by
  induction Ps generalizing Qs with
  | nil => cases Qs with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih => cases Qs with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [WP_cons, WP_cons] at hW
      obtain ⟨h1, h2⟩ := List.append_inj hW (by rw [blk_length, blk_length])
      have hxy : x = y := by
        apply Prod.ext h.1
        have h1' : codeword x.1 x.2 = codeword y.1 y.2 := h1
        rw [← h.1] at h1'
        exact inj_check x.1 x.2 y.2 h1'
      rw [hxy, ih ys h.2 h2]

theorem toPairs_fst (T : List (Fin 3)) (R : Fin T.length → Fin 2) :
    (List.ofFn fun i : Fin T.length => (T.get i, R i)).map Prod.fst = T := by
  rw [List.map_ofFn]
  exact List.ofFn_get T

theorem W_eq (T : List (Fin 3)) (R : Fin T.length → Fin 2) :
    W T R = WP (List.ofFn fun i : Fin T.length => (T.get i, R i)) := by
  unfold W WP
  rw [List.map_ofFn]
  rfl


end TernarySync.Dev.Prop31

namespace TernarySync.Alphabet
open TernarySync.Dev.Prop31 in
theorem chk_proposition_3_1 :
    IsBrinkhuisTriple 18 2 ezTriple ∧
      (∀ T : List (Fin 3), IsSquareFree T → ∀ R : Fin T.length → Fin 2, IsSquareFree (W T R)) ∧
      (∀ T : List (Fin 3), Function.Injective (W T)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
    · simp only [ezTriple]
      exact Finset.card_pair (distinct_check a)
    · intro U hU
      simp only [ezTriple, Finset.mem_insert, Finset.mem_singleton] at hU
      rcases hU with rfl | rfl <;> exact len_check _ _
    · intro a b c habc U hU V hV Z hZ
      have hab : a ≠ b := fun h => habc [a, b] ⟨[], [c], rfl⟩ ⟨[a], by simp [h]⟩
      have hbc : b ≠ c := fun h => habc [b, c] ⟨[a], [], rfl⟩ ⟨[b], by simp [h]⟩
      simp only [ezTriple, Finset.mem_insert, Finset.mem_singleton] at hU hV hZ
      have key : ∀ r t u : Fin 2,
          IsSquareFree (codeword a r ++ codeword b t ++ codeword c u) := by
        intro r t u
        have := big_check a b c hab hbc r t u
        rw [← cw_eq, ← cw_eq, ← cw_eq] at this
        exact (sqfree_iff _).2 (sqB_sound _ this)
      rcases hU with rfl | rfl <;> rcases hV with rfl | rfl <;> rcases hZ with rfl | rfl <;>
        exact key _ _ _
  · intro T hT R
    rw [W_eq]
    apply main_sqfree
    rw [toPairs_fst]; exact hT
  · intro T R R' h
    rw [W_eq, W_eq] at h
    have := WP_inj _ _ (by rw [toPairs_fst, toPairs_fst]) h
    rw [List.ofFn_inj] at this
    funext i
    exact congrArg Prod.snd (congrFun this i)
end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_proposition_3_1 := @TernarySync.Alphabet.chk_proposition_3_1
