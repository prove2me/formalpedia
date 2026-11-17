-- Prove2me | solution 1 for Vitali_set.instInfiniteQ_I_Type
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:51:09.710056+00:00
-- url     : https://prove2.me/submissions/7e22422b-e9ab-4c04-ae1d-8e7f22fa9720

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic


/- Theorem 2.9 Vitali set

There is no set function m that can accept all subsets of [0,1] as input
and return a nonnegative real number as output, such that it satisfies

* monotonicity
* countable additivity
* translation invariance (with wrapping around)
* the output of interval [a,b] is b-a, for all 0<=a<b<=1

In the proof below, we refer to such a measure as `Vitali measure`. THe conditions are
encoded in the definition `IsVitaliMeasure`. The proof is divided into a number of lemmas.
The main theorem is at the end of the file.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section Vitali_set

section Vitali_set
open Vitali_set

open Classical  -- It is essential to use choice axioms here
open Rat
open Set

-- Proof that this is indeed an equivalence relation

--  We define a Setoid on the subtype I = [0,1].
--  Two points in [0,1] are equivalent if their difference is rational.

/-!
  We define the sequence by filtering the standard enumeration of ALL rationals.
  We use 'Encodable.decode' which gives the n-th rational (if it exists).
  However, to ensure we get an infinite distinct sequence in [0,1),
  it is easier to use the fact that Q_I is infinite and Denumerable.
-/

-- Helper instance: The set of rationals in [0,1) is encodable
--Since ℚ is encodable and the predicate `0 ≤ x ∧ x < 1` is decidable,

-- Helper instance: The set of rationals in [0,1) is infinite
/-- Original source injection witness into the rational half-open interval. -/
private def source_q_in_interval (n : ℕ) : Q_I_Type :=
  ⟨(1 : ℚ) / (n + 2), by
    constructor
    · have h : (0 : ℚ) < n + 2 := by
        have : (0 : ℚ) < (2 : ℕ) := by norm_num
        have : (0 : ℚ) < (n : ℚ) + 2 := by
          have hn : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
          linarith
        exact this
      have h' := div_nonneg (show (0 : ℚ) ≤ 1 by norm_num) (le_of_lt h)
      simpa using h'
    · have hpos : (0 : ℚ) < n + 2 := by
        have : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.zero_le n)
        linarith
      have hlt : (1 : ℚ) < n + 2 := by
        have : (2 : ℚ) ≤ n + 2 := by
          have : (2 : ℕ) ≤ n + 2 := by exact Nat.le_add_left 2 n
          exact_mod_cast this
        linarith
      have h' : (1 : ℚ) / (n + 2) < 1 :=
        (div_lt_one hpos).2 hlt
      simpa using h'⟩

/-- The rational interval witness is injective. -/
private theorem source_q_in_interval_injective :
    Function.Injective source_q_in_interval := by
  intro n m h
  have hval := congrArg Subtype.val h
  change (1 : ℚ) / (n + 2) = 1 / (m + 2) at hval
  have hn : (n : ℚ) + 2 ≠ 0 := by linarith
  have hm : (m : ℚ) + 2 ≠ 0 := by linarith
  have hmul := (div_eq_div_iff hn hm).1 hval
  have h' : (m : ℚ) = n := by
    have := congrArg (fun x => x - (2 : ℚ)) hmul
    simpa using this
  norm_cast at h'
  exact h'.symm

theorem solution : Infinite Q_I_Type := by
  exact Infinite.of_injective source_q_in_interval source_q_in_interval_injective

--  The bijection between ℕ and the rationals in [0,1).
--  We use '.symm' because 'Denumerable.eqv' gives (Q_I_Type ≃ ℕ).

-- Translate of Vitali sets are disjoint

/-!
  **Helper Lemma 1**: The sequence of translated Vitali sets covers [0, 1).
-/

-- Helper: Range of translation is always in [0, 1)

-- Helper: Range of translation is subset of I

end Vitali_set
