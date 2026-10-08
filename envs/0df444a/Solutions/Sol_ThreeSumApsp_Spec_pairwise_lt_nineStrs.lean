-- Prove2me | solution 1 for ThreeSumApsp.Spec.pairwise_lt_nineStrs
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:28.827821+00:00
-- url     : https://prove2.me/submissions/10bfa3df-1edf-4249-8d47-c508dfc9a17d

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec































/-! ## The members of the list -/



















































/-- The list is strictly increasing in the lexicographic order. -/
theorem pairwise_lt_nineStrs_sourceProof (n lo hi : ℕ) : (nineStrs n lo hi).Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs <;> simp
  | succ n ih =>
    rw [nineStrs, List.pairwise_append, List.pairwise_flatMap]
    refine ⟨⟨fun d _ => ?_, ?_⟩, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (ih lo hi).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · refine List.pairwise_lt_range.imp fun {a b} hab x hx y hy => ?_
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
      exact List.cons_lt_cons_iff.2 (Or.inl hab)
    · split_ifs
      · simp
      · rw [List.pairwise_map]
        exact (ih _ _).imp fun h => List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩)
    · intro x hx y hy
      obtain ⟨d, hd, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨x', -, rfl⟩ := List.mem_map.1 hx
      split_ifs at hy
      · simp at hy
      · obtain ⟨y', -, rfl⟩ := List.mem_map.1 hy
        exact List.cons_lt_cons_iff.2 (Or.inl (List.mem_range.1 hd))




/-! ## The length of the list -/







































































/-! ## The first string -/









































/-! ## From each string to the next -/














































section

variable {n lo hi : ℕ}












































end
























section

variable {n lo hi i : ℕ}































end

end ThreeSumApsp.Spec

end


theorem solution : ∀ (n lo hi : Nat),
  @List.Pairwise.{0} (List.{0} Nat)
    (fun (x1 x2 : List.{0} Nat) => @LT.lt.{0} (List.{0} Nat) (@List.instLT.{0} Nat instLTNat) x1 x2)
    (ThreeSumApsp.Spec.nineStrs n lo hi) := by
  exact @ThreeSumApsp.Spec.pairwise_lt_nineStrs_sourceProof

#print axioms solution
