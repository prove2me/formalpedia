-- Prove2me | solution 1 for ThreeSumApsp.Spec.mem_nineStrs
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:30.667991+00:00
-- url     : https://prove2.me/submissions/03ce140c-20ec-4237-b8b6-b523df28cc03

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

/-- The first digit is below 9, or it is a 9 and counts. -/
private theorem cons_mem_nineStrs {n lo hi d : ℕ} {l : List ℕ} :
    d :: l ∈ nineStrs (n + 1) lo hi ↔
      (d < 9 ∧ l ∈ nineStrs n lo hi) ∨ (d = 9 ∧ hi ≠ 0 ∧ l ∈ nineStrs n (lo - 1) (hi - 1)) := by
  rw [nineStrs, List.mem_append, List.mem_flatMap]
  refine or_congr ?_ ?_
  · simp only [List.mem_range, List.mem_map, List.cons.injEq]
    exact ⟨fun ⟨a, ha, l', hl', had, hll⟩ => ⟨had ▸ ha, hll ▸ hl'⟩,
      fun ⟨hd, hl⟩ => ⟨d, hd, l, hl, rfl, rfl⟩⟩
  · by_cases hhi : hi = 0
    · simp [hhi]
    · simp only [if_neg hhi, List.mem_map, List.cons.injEq]
      exact ⟨fun ⟨l', hl', hd, hll⟩ => ⟨hd.symm, hhi, hll ▸ hl'⟩,
        fun ⟨hd, _, hl⟩ => ⟨l, hl, hd.symm, rfl⟩⟩

theorem mem_nineStrs_sourceProof {n lo hi : ℕ} (l : List ℕ) :
    l ∈ nineStrs n lo hi ↔
      l.length = n ∧ (∀ d ∈ l, d < 10) ∧ lo ≤ l.count 9 ∧ l.count 9 ≤ hi := by
  induction n generalizing lo hi l with
  | zero => cases l <;> by_cases h : lo = 0 <;> simp [nineStrs, h]
  | succ n ih =>
    rcases l with _ | ⟨d, l⟩
    · simp [nineStrs]
    rw [cons_mem_nineStrs, ih, ih, List.length_cons, List.forall_mem_cons,
      Nat.add_right_cancel_iff]
    by_cases hd : d = 9
    · -- a nine less is needed, and a nine less is allowed, in the rest
      subst hd
      rw [List.count_cons_self]
      grind
    · rw [List.count_cons_of_ne hd]
      grind
















































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


theorem solution : ∀ {n lo hi : Nat} (l : List.{0} Nat),
  Iff
    (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
      (ThreeSumApsp.Spec.nineStrs n lo hi) l)
    (And (@Eq.{1} Nat (@List.length.{0} Nat l) n)
      (And
        (∀ (d : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) l d →
            @LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
        (And
          (@LE.le.{0} Nat instLENat lo
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l))
          (@LE.le.{0} Nat instLENat
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l)
            hi)))) := by
  exact @ThreeSumApsp.Spec.mem_nineStrs_sourceProof

#print axioms solution
