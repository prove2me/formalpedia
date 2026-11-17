-- Prove2me | solution 1 for Vitali_set.not_exists_vitali_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:38:33.369937+00:00
-- url     : https://prove2.me/submissions/25ba6720-d6fa-4fe7-a5b9-0d8176edcbe7

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F001
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F002
import Mathlib.Data.Rat.Denumerable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.Tactic
import Theorems.Thm_Vitali_set_measure_Ico_one
import Theorems.Thm_Vitali_set_vitali_covers_Ico
import Theorems.Thm_Vitali_set_vitali_seq_disjoint


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

namespace Vitali_set
end Vitali_set
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

--  The bijection between ℕ and the rationals in [0,1).
--  We use '.symm' because 'Denumerable.eqv' gives (Q_I_Type ≃ ℕ).

-- Translate of Vitali sets are disjoint

/-!
  **Helper Lemma 1**: The sequence of translated Vitali sets covers [0, 1).
-/

-- Helper: Range of translation is always in [0, 1)

-- Helper: Range of translation is subset of I


private theorem source_vitali_nonexistence : ¬ ∃ m, IsVitaliMeasure m := by
  intro h
  rcases h with ⟨m, h_V⟩

  -- Helper: Measure of a singleton is 0
  -- have h_sing : ∀ x ∈ I, m {x} = 0 := by
  --   intro x hx
  --   exact measure_singleton_zero m h_V x hx

  have h_V_sub_I : VitaliSet ⊆ I := by
    rintro x ⟨c, rfl⟩
    exact (@Quotient.out _ vitaliSetoid c).2

  have h_disjoint : Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j))
    := by exact vitali_seq_disjoint

  have h_cover : Ico 0 1 ⊆ ⋃ n, VitaliSeq n := vitali_covers_Ico

  -- apply the countable additivity assumption
  have h_sum_eq : (∑' n, m (VitaliSeq n)) = m (⋃ n, VitaliSeq n) :=
    -- Bundle the loose hypotheses back into the structure to call the lemma
    sum_vitali_eq_union m h_V

  have h_invariant : ∀ n, m (VitaliSeq n) = m VitaliSet :=
    measure_vitali_invariant m h_V

  have h_one_le_union : 1 ≤ m (⋃ n, VitaliSeq n) := by
    rw [← measure_Ico_one m h_V]
    rcases h_V with ⟨_, _, h_mono, _, _, _⟩
    apply h_mono (Ico 0 1) (⋃ n, VitaliSeq n)
    · exact Ico_subset_Icc_self
    · apply Set.iUnion_subset; intro n; exact translate_subset_I _ _
    · exact h_cover

  have h_union_le_one : m (⋃ n, VitaliSeq n) ≤ 1 := by
    rcases h_V with ⟨_, _, h_mono, _, _, h_len⟩

    -- 1. Show m(I) = 1
    have h_m_I : m I = 1 := by
      rw [I, h_len 0 1 le_rfl zero_le_one le_rfl]
      simp

    -- 2. Rewrite the goal to match h_mono
    rw [← h_m_I]

    -- 3. Apply monotonicity
    apply h_mono (⋃ n, VitaliSeq n) I
    · -- Union is subset of I
      apply Set.iUnion_subset
      intro n
      exact translate_subset_I _ _
    · -- I is subset of I
      exact rfl.le
    · -- Union is subset of I (same as first goal)
      apply Set.iUnion_subset
      intro n
      exact translate_subset_I _ _


  let c := m VitaliSet

  -- Rewrite the sum to be explicitly ∑ c
  have h_sum_c : (∑' n, m (VitaliSeq n)) = ∑' (n : ℕ), c := by
    congr; ext n; exact h_invariant n

  rw [h_sum_c] at h_sum_eq

  by_cases hc0 : c = 0
  · -- Case c = 0
    rw [hc0, tsum_zero] at h_sum_eq  -- Sum of zeros is 0
    rw [← h_sum_eq] at h_one_le_union
    -- We have 1 ≤ 0, contradiction
    exact not_le_of_gt zero_lt_one h_one_le_union
  · -- If c > 0, the infinite sum of c is ∞ (top).
    -- This implies m(Union) = ∞.
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hc0] at h_sum_eq -- Sum is ∞
    rw [← h_sum_eq] at h_union_le_one
    -- We know 1 < ⊤, so ⊤ ≤ 1 is impossible.
    apply not_le_of_gt ENNReal.one_lt_top h_union_le_one
theorem solution : ¬ ∃ m, IsVitaliMeasure m := by
  exact source_vitali_nonexistence
end Vitali_set
