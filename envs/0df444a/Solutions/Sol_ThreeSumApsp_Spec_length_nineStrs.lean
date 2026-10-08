-- Prove2me | solution 1 for ThreeSumApsp.Spec.length_nineStrs
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:31.626966+00:00
-- url     : https://prove2.me/submissions/45e1abfd-973c-4430-9d97-908f467c5ef9

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

















































































/-! ## The length of the list -/

/-- The recursion for the length of the list. -/
private theorem length_nineStrs_succ (n lo hi : ℕ) :
    (nineStrs (n + 1) lo hi).length = 9 * (nineStrs n lo hi).length
      + if hi = 0 then 0 else (nineStrs n (lo - 1) (hi - 1)).length := by
  rw [nineStrs, List.length_append, List.length_flatMap]
  congr 1
  · simp only [List.length_map, List.map_const', List.length_range, List.sum_replicate_nat]
  · split_ifs <;> simp

/-- Strings without a nine: one more digit, nine times as many. -/
private theorem nineTerm_zero (n : ℕ) :
    (n + 1).choose 0 * 9 ^ (n + 1 - 0) = 9 * (n.choose 0 * 9 ^ (n - 0)) := by
  simp [pow_succ, mul_comm]

/-- Strings with g + 1 nines: the first digit is a nine or one of the nine other digits. -/
private theorem nineTerm_succ (n g : ℕ) :
    (n + 1).choose (g + 1) * 9 ^ (n + 1 - (g + 1))
      = n.choose g * 9 ^ (n - g) + 9 * (n.choose (g + 1) * 9 ^ (n - (g + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right, add_mul]
  congr 1
  rcases Nat.lt_or_ge n (g + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    simp
  · rw [show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring

/-- A sum from 0: the first summand apart. -/
private theorem sum_Icc_zero_succ (h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc 0 (h + 1), G f = G 0 + ∑ g ∈ Finset.Icc 0 h, G (g + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ', add_comm]

/-- A sum with both ends shifted by one. -/
private theorem sum_Icc_succ_succ (l h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc (l + 1) (h + 1), G f = ∑ g ∈ Finset.Icc l h, G (g + 1) := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- There are binom(n, f) 9^{n-f} strings with exactly f nines. -/
theorem length_nineStrs_sourceProof (n lo hi : ℕ) :
    (nineStrs n lo hi).length = ∑ f ∈ Finset.Icc lo hi, n.choose f * 9 ^ (n - f) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single_of_mem 0 (by simp) fun b _ hb => by
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), zero_mul]]
      rfl
    · refine (Finset.sum_eq_zero fun f hf => ?_).symm
      have := (Finset.mem_Icc.1 hf).1
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  | succ n ih =>
    rw [length_nineStrs_succ, ih]
    rcases hi with _ | h
    · -- no nine is allowed
      rw [if_pos rfl, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      obtain rfl : f = 0 := Nat.le_zero.mp (Finset.mem_Icc.1 hf).2
      exact (nineTerm_zero n).symm
    · rw [if_neg (Nat.succ_ne_zero h), ih, Nat.add_sub_cancel]
      rcases lo with _ | l
      · rw [sum_Icc_zero_succ, sum_Icc_zero_succ, nineTerm_zero, Nat.zero_sub, mul_add,
          Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        rw [nineTerm_succ, add_comm]
      · rw [sum_Icc_succ_succ, sum_Icc_succ_succ, Nat.add_sub_cancel, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [nineTerm_succ, add_comm]

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
  @Eq.{1} Nat (@List.length.{0} (List.{0} Nat) (ThreeSumApsp.Spec.nineStrs n lo hi))
    (∑ f ∈ @Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder lo hi,
      @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (n.choose f)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n f))) := by
  exact @ThreeSumApsp.Spec.length_nineStrs_sourceProof

#print axioms solution
