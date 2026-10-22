-- Prove2me | solution 1 for SecretaryAdvice.SamplesDual.t_forms
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:00:49.356916+00:00
-- url     : https://prove2.me/submissions/a1015d22-74b3-436f-902b-2729ff2990e4

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

set_option autoImplicit false
open Finset
open SecretaryAdvice.SamplesDual

lemma SAD_hockey (N j : ℕ) (hj : 1 ≤ j) :
    ∑ m ∈ Icc 1 N, (m.choose j : ℝ) = ((N + 1).choose (j + 1) : ℝ) := by
  have h := Nat.sum_Icc_choose N j
  have h2 : ∑ m ∈ Icc 1 N, (m.choose j : ℝ) = ∑ m ∈ Icc j N, (m.choose j : ℝ) := by
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [mem_Icc] at hm ⊢
      omega
    · intro m hm hm'
      simp only [mem_Icc] at hm hm'
      have : m < j := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  rw [h2]
  exact_mod_cast h

lemma SAD_reindex (n i : ℕ) (hin : i < n) (f : ℕ → ℝ) :
    ∑ z ∈ Icc (i + 1) (n - 1), f (n - z) = ∑ m ∈ Icc 1 (n - i - 1), f m := by
  apply Finset.sum_nbij' (fun z => n - z) (fun m => n - m)
  · intro z hz; simp only [mem_Icc] at hz ⊢; omega
  · intro m hm; simp only [mem_Icc] at hm ⊢; omega
  · intro z hz; simp only [mem_Icc] at hz; omega
  · intro m hm; simp only [mem_Icc] at hm; omega
  · intro z _; rfl

theorem solution (n k i s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s' ≤ k) :
    T n k i s' =
      ((n : ℝ) - i) * (∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) -
        ∑ j ∈ Icc 1 (n - i - 1),
          ((n : ℝ) - i) * ((n - i - 1).choose j : ℝ) * (1 / ((j : ℝ) * ((j : ℝ) + 1))) *
            (∏ ℓ ∈ Icc 1 j, ((k : ℝ) - s' + ℓ)) *
            (∏ t ∈ Icc (i + 1) (n - j - 1), ((s' : ℝ) + t)) := by
  unfold T
  congr 1
  set A : ℕ → ℝ := fun j => ∏ ℓ ∈ Icc 1 j, ((k : ℝ) - s' + ℓ) with hA
  set B : ℕ → ℝ := fun j => ∏ t ∈ Icc (i + 1) (n - j - 1), ((s' : ℝ) + t) with hB
  have h1 : ∀ z ∈ Icc (i + 1) (n - 1),
      ∑ j ∈ Icc 1 (n - z), ((n - z).choose j : ℝ) * (1 / (j : ℝ)) * A j * B j =
      ∑ j ∈ Icc 1 (n - i - 1), ((n - z).choose j : ℝ) * (1 / (j : ℝ)) * A j * B j := by
    intro z hz
    simp only [mem_Icc] at hz
    apply Finset.sum_subset
    · intro j hj; simp only [mem_Icc] at hj ⊢; omega
    · intro j hj hj'
      simp only [mem_Icc] at hj hj'
      have : n - z < j := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mem_Icc] at hj
  have h2 : ∑ z ∈ Icc (i + 1) (n - 1), ((n - z).choose j : ℝ) = ((n - i).choose (j + 1) : ℝ) := by
    rw [SAD_reindex n i hin (fun m => (m.choose j : ℝ)), SAD_hockey _ j hj.1]
    congr 3
    omega
  have h3 : ∀ z : ℕ, ((n - z).choose j : ℝ) * (1 / (j : ℝ)) * A j * B j =
      ((n - z).choose j : ℝ) * ((1 / (j : ℝ)) * A j * B j) := by intro z; ring
  simp only [h3, ← Finset.sum_mul, h2]
  have h4 : ((n - i).choose (j + 1) : ℝ) * ((j : ℝ) + 1) = ((n : ℝ) - i) * ((n - i - 1).choose j : ℝ) := by
    have e : n - i = (n - i - 1) + 1 := by omega
    have := Nat.add_one_mul_choose_eq (n - i - 1) j
    have h5 : ((n - i - 1 + 1 : ℕ) : ℝ) * ((n - i - 1).choose j : ℝ) =
        (((n - i - 1) + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by exact_mod_cast this
    rw [← e] at h5
    have h6 : ((n - i : ℕ) : ℝ) = (n : ℝ) - i := by
      rw [Nat.cast_sub hin.le]
    rw [h6] at h5
    linarith
  have hj0 : (j : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    linarith
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h7 : ((n - i).choose (j + 1) : ℝ) = ((n : ℝ) - i) * ((n - i - 1).choose j : ℝ) / ((j : ℝ) + 1) := by
    field_simp
    linarith
  rw [h7]
  simp only [hA, hB]
  field_simp
