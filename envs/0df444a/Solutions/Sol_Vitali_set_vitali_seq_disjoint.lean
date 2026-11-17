-- Prove2me | solution 1 for Vitali_set.vitali_seq_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:58.374002+00:00
-- url     : https://prove2.me/submissions/27c09f45-84ee-4467-9705-b6150ced3fc8

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
/-- Uniqueness of the chosen representative in each Vitali equivalence class. -/
private theorem source_vitali_representative_unique
    {v1 v2 : ℝ} (hv1 : v1 ∈ VitaliSet) (hv2 : v2 ∈ VitaliSet)
    (h_rel : vitali_rel v1 v2) : v1 = v2 := by
  rcases hv1 with ⟨c1, rfl⟩
  rcases hv2 with ⟨c2, rfl⟩
  let v1_sub : I := @Quotient.out _ vitaliSetoid c1
  let v2_sub : I := @Quotient.out _ vitaliSetoid c2
  have h_equiv : v1_sub ≈ v2_sub := h_rel
  have h_mk_eq :
      Quotient.mk vitaliSetoid v1_sub = Quotient.mk vitaliSetoid v2_sub :=
    Quotient.sound h_equiv
  rw [Quotient.out_eq c1] at h_mk_eq
  rw [Quotient.out_eq c2] at h_mk_eq
  rw [h_mk_eq]

/-- An integral shift between two rational unit fractions is zero. -/
private theorem source_q_seq_integer_zero (i j : ℕ) (k : ℤ)
    (h_k_eq : q_seq j - q_seq i + k = (0 : ℝ)) : k = 0 := by
  have hi : 0 ≤ q_seq i ∧ q_seq i < 1 := by
    have h := (q_bij i).2
    simp [q_seq]; norm_cast
  have hj : 0 ≤ q_seq j ∧ q_seq j < 1 := by
    have h := (q_bij j).2
    simp [q_seq]; norm_cast
  have h_bound : -1 < (k : ℝ) ∧ (k : ℝ) < 1 := by
    rcases hi with ⟨hi_lo, hi_hi⟩
    rcases hj with ⟨hj_lo, hj_hi⟩
    have : (k : ℝ) = q_seq i - q_seq j := by linarith [h_k_eq]
    rw [this]
    constructor <;> linarith
  norm_cast at h_bound
  rcases h_bound with ⟨h_gt, h_lt⟩
  change -1 < k at h_gt
  rw [← zero_add 1, Int.lt_add_one_iff] at h_lt
  rw [← Int.add_one_le_iff] at h_gt
  norm_num at h_gt
  linarith

/-- Two different rational translates of the Vitali representatives do not intersect. -/
private theorem source_vitali_no_inter
    (i j : ℕ) (hij : i ≠ j) (x v1 v2 : ℝ)
    (hv1 : v1 ∈ VitaliSet) (hv2 : v2 ∈ VitaliSet)
    (hx1 : Int.fract (v1 + q_seq i) = x)
    (hx2 : Int.fract (v2 + q_seq j) = x) : False := by
  have h_fract_eq :
      Int.fract (v1 + q_seq i) = Int.fract (v2 + q_seq j) := by
    rw [hx1, ← hx2]
  rw [Int.fract_eq_fract] at h_fract_eq
  rcases h_fract_eq with ⟨k, hk⟩
  have h_diff : v1 - v2 = q_seq j - q_seq i + k := by linarith
  have h_rel : vitali_rel v1 v2 := by
    use (q_bij j).val - (q_bij i).val + k
    rw [h_diff]; simp [q_seq]
  have h_v_eq : v1 = v2 := source_vitali_representative_unique hv1 hv2 h_rel
  subst h_v_eq
  have h_k_eq : q_seq j - q_seq i + k = 0 := by linarith [hk]
  have h_k_zero : k = 0 := source_q_seq_integer_zero i j k h_k_eq
  rw [h_k_zero] at h_k_eq
  simp only [Int.cast_zero, add_zero, sub_eq_zero] at h_k_eq
  have h_idx : i = j := by
    unfold q_seq at h_k_eq
    norm_cast at h_k_eq
    apply q_bij.injective
    apply Subtype.ext
    exact h_k_eq.symm
  exact hij h_idx

theorem solution :
    Pairwise (fun i j => Disjoint (VitaliSeq i) (VitaliSeq j)) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [VitaliSeq, translate, mem_inter_iff, mem_image, Set.mem_empty_iff_false, iff_false]
  intro h_inter
  rcases h_inter with ⟨h_i, h_j⟩
  rcases h_i with ⟨v1, hv1_mem, hx1⟩
  rcases h_j with ⟨v2, hv2_mem, hx2⟩
  exact source_vitali_no_inter i j hij x v1 v2 hv1_mem hv2_mem hx1 hx2

/-!
  **Helper Lemma 1**: The sequence of translated Vitali sets covers [0, 1).
-/

-- Helper: Range of translation is always in [0, 1)

-- Helper: Range of translation is subset of I

end Vitali_set
