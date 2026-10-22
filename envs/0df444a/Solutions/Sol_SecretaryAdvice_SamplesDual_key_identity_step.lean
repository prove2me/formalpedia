-- Prove2me | solution 1 for SecretaryAdvice.SamplesDual.key_identity_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:22:32.845303+00:00
-- url     : https://prove2.me/submissions/df1abe98-8bfe-4c58-8598-ba3c8dc4f6dc

import Mathlib
import Definitions.Def_SecretaryAdvice_SamplesDual_ClosedForm

set_option autoImplicit false
open Finset
open SecretaryAdvice.SamplesDual

/-- `∏_{ℓ=1}^{j} (a + ℓ)` -/
noncomputable def SADP (a : ℝ) (j : ℕ) : ℝ := ∏ ℓ ∈ Icc 1 j, (a + ℓ)

/-- rising factorial `y (y+1) ... (y+r-1)` -/
noncomputable def SADQ (y : ℝ) (r : ℕ) : ℝ := ∏ u ∈ range r, (y + u)

lemma SADP_zero (a : ℝ) : SADP a 0 = 1 := by simp [SADP]

lemma SADP_succ (a : ℝ) (j : ℕ) : SADP a (j + 1) = SADP a j * (a + ((j : ℝ) + 1)) := by
  unfold SADP
  rw [Finset.prod_Icc_succ_top (by omega)]
  push_cast
  ring

lemma SADQ_zero (y : ℝ) : SADQ y 0 = 1 := by simp [SADQ]

lemma SADQ_succ (y : ℝ) (r : ℕ) : SADQ y (r + 1) = SADQ y r * (y + r) := by
  unfold SADQ
  rw [Finset.prod_range_succ]

lemma SADQ_succ' (y : ℝ) (r : ℕ) : SADQ y (r + 1) = y * SADQ (y + 1) r := by
  unfold SADQ
  have : ∏ k ∈ range r, (y + ((k + 1 : ℕ) : ℝ)) = ∏ u ∈ range r, (y + 1 + (u : ℝ)) :=
    Finset.prod_congr rfl (fun u _ => by push_cast; ring)
  rw [Finset.prod_range_succ', this, Nat.cast_zero, add_zero, mul_comm]

lemma SAD_prodIcc (f : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) :
    ∀ r : ℕ, ∏ t ∈ Icc i (i + r - 1), f t = ∏ u ∈ range r, f (i + u) := by
  intro r
  induction r with
  | zero =>
    rw [Finset.Icc_eq_empty (by omega)]
    simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ← ih]
    have : i + (r + 1) - 1 = (i + r - 1) + 1 := by omega
    rw [this, Finset.prod_Icc_succ_top (by omega)]
    congr 2
    omega

lemma SAD_sumIcc1 (N : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Icc 1 N, f j = ∑ j ∈ range N, f (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma SAD_coef (M : ℕ) (w : ℕ → ℝ) :
    w M + ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) *
        (((j : ℝ) + 1) * w j - ((M : ℝ) - j) * w (j + 1)) =
      ((M : ℝ) + 1) * w 0 - ∑ j ∈ range M, ((M : ℝ) + 1) * (M.choose (j + 1) : ℝ) /
        (((j : ℝ) + 1) * ((j : ℝ) + 2)) * w (j + 1) := by
  set f : ℕ → ℝ := fun j => ((M + 1).choose (j + 1) : ℝ) * w j with hf
  have hterm : ∀ j ∈ range M,
      ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) *
        (((j : ℝ) + 1) * w j - ((M : ℝ) - j) * w (j + 1)) +
      ((M : ℝ) + 1) * (M.choose (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * w (j + 1)
      = f j - f (j + 1) := by
    intro j hj
    have hjM : j ≤ M := (Finset.mem_range.1 hj).le
    have hA : ((M + 1).choose (j + 1) : ℝ) * ((M : ℝ) - j) =
        ((M + 1).choose (j + 2) : ℝ) * ((j : ℝ) + 2) := by
      have h := Nat.choose_succ_right_eq (M + 1) (j + 1)
      have h' : (((M + 1).choose (j + 1 + 1) : ℕ) : ℝ) * ((j + 1 + 1 : ℕ) : ℝ) =
          (((M + 1).choose (j + 1) : ℕ) : ℝ) * ((M + 1 - (j + 1) : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub (by omega)] at h'
      push_cast at h'
      linarith
    have hB : ((M : ℝ) + 1) * (M.choose (j + 1) : ℝ) =
        ((M + 1).choose (j + 2) : ℝ) * ((j : ℝ) + 2) := by
      have := Nat.add_one_mul_choose_eq M (j + 1)
      have h2 : ((M + 1 : ℕ) : ℝ) * (M.choose (j + 1) : ℝ) =
          (((M + 1).choose (j + 1 + 1) : ℕ) : ℝ) * ((j + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h2
      linarith
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have hj2 : ((j : ℝ) + 2) ≠ 0 := by positivity
    have e1 : ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) *
        (((j : ℝ) + 1) * w j - ((M : ℝ) - j) * w (j + 1)) =
        ((M + 1).choose (j + 1) : ℝ) * w j -
          ((M + 1).choose (j + 2) : ℝ) * ((j : ℝ) + 2) / ((j : ℝ) + 1) * w (j + 1) := by
      field_simp
      linear_combination (-(w (j + 1))) * hA
    have e2 : ((M : ℝ) + 1) * (M.choose (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) * w (j + 1) =
        ((M + 1).choose (j + 2) : ℝ) / ((j : ℝ) + 1) * w (j + 1) := by
      field_simp
      linear_combination (w (j + 1)) * hB
    rw [e1, e2]
    simp only [hf]
    field_simp
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib, Finset.sum_range_sub'] at hsum
  simp only [hf, zero_add, Nat.choose_one_right, Nat.choose_self] at hsum
  push_cast at hsum
  linarith

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


lemma SAD_t_forms (n k i s' : ℕ) (hin : i < n) :
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


lemma SADP_shift (a : ℝ) : ∀ j : ℕ, SADP (a - 1) (j + 1) = a * SADP a j := by
  intro j
  induction j with
  | zero => simp [SADP]
  | succ j ih =>
    rw [SADP_succ, ih, SADP_succ]
    push_cast
    ring

lemma SAD_keyRHS_eq (M k i s : ℕ) (hi : 1 ≤ i) :
    keyRHS (i + M + 1) k i s =
      ∑ j ∈ range (M + 1), ((M + 1).choose (j + 1) : ℝ) * (1 / ((j : ℝ) + 1)) *
        SADP ((k : ℝ) - s) (j + 1) * SADQ ((s : ℝ) + i) (M - j) := by
  unfold keyRHS
  have e1 : i + M + 1 - i = M + 1 := by omega
  rw [e1, SAD_sumIcc1]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < M + 1 := Finset.mem_range.1 hj
  have e2 : i + M + 1 - (j + 1) - 1 = i + (M - j) - 1 := by omega
  rw [e2, SAD_prodIcc (fun t => (s : ℝ) + t) i hi (M - j)]
  have e3 : ∏ u ∈ range (M - j), ((s : ℝ) + ((i + u : ℕ) : ℝ)) = SADQ ((s : ℝ) + i) (M - j) := by
    unfold SADQ
    apply Finset.prod_congr rfl
    intro u _
    push_cast
    ring
  simp only [e3, SADP]
  push_cast
  ring

lemma SAD_T_eq (M k i s : ℕ) (hi : 1 ≤ i) :
    T (i + M + 1) k i s =
      ((M : ℝ) + 1) * SADQ ((s : ℝ) + i + 1) M -
        ∑ j ∈ range M, ((M : ℝ) + 1) * (M.choose (j + 1) : ℝ) /
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) *
          (SADP ((k : ℝ) - s) (j + 1) * SADQ ((s : ℝ) + i + 1) (M - (j + 1))) := by
  rw [SAD_t_forms (i + M + 1) k i s (by omega)]
  have e0 : i + M + 1 - i - 1 = M := by omega
  have e1 : i + M + 1 - 1 = (i + 1) + M - 1 := by omega
  rw [e0, e1, SAD_prodIcc (fun t => (s : ℝ) + t) (i + 1) (by omega) M, SAD_sumIcc1]
  have e3 : ∏ u ∈ range M, ((s : ℝ) + ((i + 1 + u : ℕ) : ℝ)) = SADQ ((s : ℝ) + i + 1) M := by
    unfold SADQ
    apply Finset.prod_congr rfl
    intro u _
    push_cast
    ring
  rw [e3]
  have e4 : ((i + M + 1 : ℕ) : ℝ) - i = (M : ℝ) + 1 := by push_cast; ring
  rw [e4]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < M := Finset.mem_range.1 hj
  have e5 : i + M + 1 - (j + 1) - 1 = (i + 1) + (M - (j + 1)) - 1 := by omega
  rw [e5, SAD_prodIcc (fun t => (s : ℝ) + t) (i + 1) (by omega) (M - (j + 1))]
  have e6 : ∏ u ∈ range (M - (j + 1)), ((s : ℝ) + ((i + 1 + u : ℕ) : ℝ)) =
      SADQ ((s : ℝ) + i + 1) (M - (j + 1)) := by
    unfold SADQ
    apply Finset.prod_congr rfl
    intro u _
    push_cast
    ring
  rw [e6]
  simp only [SADP]
  push_cast
  field_simp
  ring

lemma SAD_wrel (a c : ℝ) (M j : ℕ) (hj : j < M) :
    c * (SADP a (j + 1) * SADQ (c + 1) (M - (j + 1))) - a * (SADP a j * SADQ (c + 1) (M - j)) =
      ((j : ℝ) + 1) * (SADP a j * SADQ (c + 1) (M - j)) -
        ((M : ℝ) - j) * (SADP a (j + 1) * SADQ (c + 1) (M - (j + 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, M = j + 1 + r := ⟨M - (j + 1), by omega⟩
  have e1 : j + 1 + r - j = r + 1 := by omega
  have e2 : j + 1 + r - (j + 1) = r := by omega
  rw [e1, e2, SADP_succ, SADQ_succ]
  push_cast
  ring

lemma SAD_master (M k i s : ℕ) (hi : 1 ≤ i) :
    keyRHS (i + M + 1) k i s - keyRHS (i + M + 1) k i (s + 1) = T (i + M + 1) k i s := by
  rw [SAD_keyRHS_eq M k i s hi, SAD_keyRHS_eq M k i (s + 1) hi, SAD_T_eq M k i s hi]
  have h1 : (k : ℝ) - ((s + 1 : ℕ) : ℝ) = ((k : ℝ) - s) - 1 := by push_cast; ring
  have h2 : ((s + 1 : ℕ) : ℝ) + i = ((s : ℝ) + i) + 1 := by push_cast; ring
  rw [h1, h2]
  generalize ((k : ℝ) - s) = a
  generalize ((s : ℝ) + i) = c
  set w : ℕ → ℝ := fun l => SADP a l * SADQ (c + 1) (M - l) with hw
  have hR0 : ∑ j ∈ range (M + 1), ((M + 1).choose (j + 1) : ℝ) * (1 / ((j : ℝ) + 1)) *
        SADP a (j + 1) * SADQ c (M - j) =
      ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) * (c * w (j + 1)) +
        SADP a (M + 1) / ((M : ℝ) + 1) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < M := Finset.mem_range.1 hj
      obtain ⟨r, hr⟩ : ∃ r, M - j = r + 1 := ⟨M - j - 1, by omega⟩
      have hr' : M - (j + 1) = r := by omega
      rw [hr, SADQ_succ']
      simp only [hw, hr']
      field_simp
    · simp [SADQ_zero]
      field_simp
  have hR1 : ∑ j ∈ range (M + 1), ((M + 1).choose (j + 1) : ℝ) * (1 / ((j : ℝ) + 1)) *
        SADP (a - 1) (j + 1) * SADQ (c + 1) (M - j) =
      ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) * (a * w j) +
        a * w M / ((M : ℝ) + 1) := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [SADP_shift]
      simp only [hw]
      field_simp
    · rw [SADP_shift]
      simp only [hw]
      simp
      field_simp
  have hlast : SADP a (M + 1) / ((M : ℝ) + 1) - a * w M / ((M : ℝ) + 1) = w M := by
    simp only [hw, Nat.sub_self, SADQ_zero, mul_one]
    rw [SADP_succ]
    have : ((M : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have hmid : ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) * (c * w (j + 1)) -
      ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) * (a * w j) =
      ∑ j ∈ range M, ((M + 1).choose (j + 1) : ℝ) / ((j : ℝ) + 1) *
        (((j : ℝ) + 1) * w j - ((M : ℝ) - j) * w (j + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have := SAD_wrel a c M j (Finset.mem_range.1 hj)
    simp only [hw]
    rw [← mul_sub, this]
  have hcoef := SAD_coef M w
  have hw0 : w 0 = SADQ (c + 1) M := by simp [hw, SADP_zero]
  rw [hR0, hR1]
  have hq : ∀ j : ℕ, SADP a (j + 1) * SADQ (c + 1) (M - (j + 1)) = w (j + 1) := fun j => rfl
  simp only [hq]
  rw [← hw0]
  linarith

lemma SAD_master' (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    keyRHS n k i s - keyRHS n k i (s + 1) = T n k i s := by
  obtain ⟨M, rfl⟩ : ∃ M, n = i + M + 1 := ⟨n - i - 1, by omega⟩
  exact SAD_master M k i s hi

lemma SAD_key_top (n k i : ℕ) : keyRHS n k i (k + 1) = 0 := by
  unfold keyRHS
  apply Finset.sum_eq_zero
  intro j hj
  have h1 : (1 : ℕ) ∈ Icc 1 j := by
    simp only [mem_Icc] at hj ⊢
    omega
  have h0 : ∏ ℓ ∈ Icc 1 j, ((k : ℝ) - ((k + 1 : ℕ) : ℝ) + ℓ) = 0 := by
    apply Finset.prod_eq_zero h1
    push_cast
    ring
  rw [h0]
  ring

lemma SAD_sum_split (n k i s : ℕ) (hs : s ≤ k) :
    ∑ s' ∈ Icc s k, T n k i s' = T n k i s + ∑ s' ∈ Icc (s + 1) k, T n k i s' := by
  rw [← Finset.insert_Icc_add_one_left_eq_Icc hs, Finset.sum_insert (by simp)]

theorem solution (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s < k)
    (h : ∑ s' ∈ Icc (s + 1) k, T n k i s' = keyRHS n k i (s + 1)) :
    ∑ s' ∈ Icc s k, T n k i s' = keyRHS n k i s := by
  rw [SAD_sum_split n k i s hs.le, h]
  have := SAD_master' n k i s hi hin
  linarith
