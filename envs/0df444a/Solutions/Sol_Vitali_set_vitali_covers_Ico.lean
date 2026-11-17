-- Prove2me | solution 1 for Vitali_set.vitali_covers_Ico
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:53:47.485265+00:00
-- url     : https://prove2.me/submissions/2c0b63a5-24a2-4596-bba7-e29814307b24

import Theorems.Thm_Vitali_set_instInfiniteQ_I_Type
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_9_F001
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

--  The bijection between ℕ and the rationals in [0,1).
--  We use '.symm' because 'Denumerable.eqv' gives (Q_I_Type ≃ ℕ).

-- Translate of Vitali sets are disjoint

/-!
  **Helper Lemma 1**: The sequence of translated Vitali sets covers [0, 1).
-/
/-- The fractional part of a rational real difference is rational. -/
private theorem source_fract_rat_witness (x y : ℝ) (q : ℚ)
    (h_diff : x - y = (q : ℝ)) :
    ∃ q_rat : ℚ, (q_rat : ℝ) = Int.fract (x - y) := by
  use Int.fract q
  rw [h_diff]
  simp only [Int.fract]
  rw [Rat.cast_sub]
  rw [Rat.cast_intCast]
  rw [Rat.floor_cast]

/-- Fractional translation recovers a point of the unit half-open interval. -/
private theorem source_fract_shift_self (x y : ℝ) (hx : x ∈ Set.Ico 0 1) :
    Int.fract (y + Int.fract (x - y)) = x := by
  have h_arith : y + Int.fract (x - y) = x - ↑⌊x - y⌋ := by
    rw [Int.fract]
    ring
  rw [h_arith]
  rw [Int.fract_sub_intCast]
  exact Int.fract_eq_self.mpr hx

/-- A rational identified with the fractional part lies in [0,1). -/
private theorem source_rat_fract_mem_unit
    (x y : ℝ) (q_rat : ℚ)
    (h_q_eq : (q_rat : ℝ) = Int.fract (x - y)) :
    0 ≤ q_rat ∧ q_rat < 1 := by
  rw [← Rat.cast_le (K := ℝ), ← Rat.cast_lt (K := ℝ), h_q_eq]
  simp only [Rat.cast_zero, Rat.cast_one]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Pick a representative of the Vitali class of x, with rational difference. -/
private theorem source_vitali_related_point
    (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    ∃ y : ℝ, y ∈ VitaliSet ∧ ∃ q_diff : ℚ, x - y = (q_diff : ℝ) := by
  let c := Quotient.mk vitaliSetoid ⟨x, Ico_subset_Icc_self hx⟩
  let y_sub := @Quotient.out _ vitaliSetoid c
  let y := y_sub.val
  have hy : y ∈ VitaliSet := by
    use c
  have h_equiv : ⟨x, Ico_subset_Icc_self hx⟩ ≈ y_sub :=
    Quotient.eq.mp (Quotient.out_eq c).symm
  rcases h_equiv with ⟨q_diff, h_diff⟩
  exact ⟨y, hy, q_diff, h_diff⟩

theorem solution : Ico 0 1 ⊆ ⋃ n, VitaliSeq n := by
  intro x hx
  rcases source_vitali_related_point x hx with ⟨y, hy, q_diff, h_diff⟩

  -- 4. Consider the fractional part of the difference: fract(x - y)
  -- Since x - y is rational, its fractional part is also rational.
  let q_frac := Int.fract (x - y)

  have h_q_rat : ∃ q_rat : ℚ, (q_rat : ℝ) = q_frac := by
    simpa [q_frac] using source_fract_rat_witness x y q_diff h_diff

  rcases h_q_rat with ⟨q_rat, h_q_eq⟩

  -- 5. Show this rational is in our enumeration range [0, 1)
  have h_mem_Q_I : 0 ≤ q_rat ∧ q_rat < 1 :=
    source_rat_fract_mem_unit x y q_rat (by simpa [q_frac] using h_q_eq)
  -- 6. Find the index n such that q_seq n = fract(x - y)
  let q_elt : Q_I_Type := ⟨q_rat, h_mem_Q_I⟩
  let n := q_bij.symm q_elt

  refine mem_iUnion.2 ⟨n, ?_⟩

  -- 7. Show x is in translate VitaliSet (q_seq n)
  use y, hy
  -- We need to prove: x = fract(y + q_seq n)
  rw [q_seq]
  -- Expand the definition of n to see (q_bij.symm q_elt)
  dsimp only [n]
  -- Apply the property: q_bij (q_bij.symm x) = x
  rw [q_bij.apply_symm_apply]
  rw [h_q_eq]

  simpa [q_frac] using source_fract_shift_self x y hx
-- Helper: Range of translation is always in [0, 1)

-- Helper: Range of translation is subset of I

end Vitali_set
