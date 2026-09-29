-- Prove2me | solution 1 for PaigeTarjan.LexSort.no_proper_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:37:56.37124+00:00
-- url     : https://prove2.me/submissions/9c7041be-e3b6-4476-9be5-7e2fd3382871

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic

open PaigeTarjan.LexSort

/-- §2, p. 974: because the end marker `0` occurs only in the last position of a string, no
string in `U` is a proper prefix of another string in `U`. -/
theorem solution {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hx : EndMarked x)
    (i j : Fin n) (hij : x i <+: x j) : x i = x j := by
  classical
  obtain ⟨t, ht⟩ := hij
  obtain ⟨w, hw, h0w⟩ := hx i
  obtain ⟨w', hw', h0w'⟩ := hx j
  cases t with
  | nil => simpa using ht
  | cons a t' =>
      -- `x i ++ (a :: t') = x j` together with `x i = w ++ [0]` gives
      -- `x j = w ++ (0 :: a :: t')`: the symbol at position `w.length` of `x j` is `0`.
      have hxj : w ++ (0 :: a :: t') = w' ++ [0] := by
        simpa [hw, hw'] using ht
      have hpos : (w' ++ [0])[w.length]? = some 0 := by
        rw [← hxj, List.getElem?_append_right (by simp)]
        simp
      -- If `w.length < w'.length` that position lies strictly inside `w'`, so
      -- `0 ∈ w'`, contradicting the end-marked form of `x j`.
      have hle : w'.length ≤ w.length := by
        by_contra hn
        have hlt : w.length < w'.length := by simpa using Nat.not_le.mp hn
        rw [List.getElem?_append_left hlt] at hpos
        exact absurd (List.mem_of_getElem? hpos) h0w'
      -- Taking lengths in `x j = w ++ (0 :: a :: t') = w' ++ [0]` forces
      -- `w'.length = w.length + 1 + t'.length > w.length`, contradicting `hle`.
      have hlen : w.length + 2 + t'.length = w'.length + 1 := by
        have h := congrArg List.length hxj
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_singleton] at h
        omega
      omega
