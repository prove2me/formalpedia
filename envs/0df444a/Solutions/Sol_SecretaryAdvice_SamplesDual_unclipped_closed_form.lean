-- Prove2me | solution 1 for SecretaryAdvice.SamplesDual.unclipped_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:26:59.528861+00:00
-- url     : https://prove2.me/submissions/2c2296fe-31ee-4f8e-b2f6-9a7a2d515f74

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

theorem SAD_keyid (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) (hs : s ≤ k) :
    ∑ s' ∈ Icc s k, T n k i s' = keyRHS n k i s := by
  obtain ⟨d, hd⟩ : ∃ d, s + d = k := ⟨k - s, by omega⟩
  induction d generalizing s with
  | zero =>
    have : s = k := by omega
    subst this
    rw [Finset.Icc_self, Finset.sum_singleton]
    have := SAD_master' n s i s hi hin
    rw [SAD_key_top] at this
    linarith
  | succ d ih =>
    have h1 := ih (s + 1) (by omega) (by omega)
    rw [SAD_sum_split n k i s hs, h1]
    have := SAD_master' n k i s hi hin
    linarith

lemma tred_unfold (n k i : ℕ) (hin : i < n) (s : Fin (k + 1)) :
    samplesUnclipped n k i s = coeffA n k s - ∑ j ∈ Ioc i n, ∑ s' : Fin (k + 1),
      samplesUnclipped n k j s' * coeffC s' i s := by
  unfold samplesUnclipped
  rw [unclippedDual, if_pos hin]
  congr 1
  exact Finset.sum_attach (Finset.Ioc i n) (fun j => ∑ s' : Fin (k + 1),
      unclippedDual n (S := Fin (k + 1)) (fun _ s => coeffA n k s) (fun _ s' i s => coeffC s' i s) j s' *
        coeffC s' i s)



lemma SADQ_add (y : ℝ) (r1 r2 : ℕ) : SADQ y (r1 + r2) = SADQ y r1 * SADQ (y + r1) r2 := by
  unfold SADQ
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  push_cast
  ring

lemma SADQ_pos (y : ℝ) (hy : 0 < y) (r : ℕ) : 0 < SADQ y r := by
  unfold SADQ
  apply Finset.prod_pos
  intro u _
  have : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  linarith

lemma SAD_Icc_to_Q (x : ℝ) (a r b : ℕ) (ha : 1 ≤ a) (hb : b + 1 = a + r) :
    ∏ t ∈ Icc a b, (x + (t : ℝ)) = SADQ (x + a) r := by
  have hb' : b = a + r - 1 := by omega
  rw [hb', SAD_prodIcc (fun t => x + (t : ℝ)) a ha r]
  unfold SADQ
  apply Finset.prod_congr rfl
  intro u _
  push_cast
  ring

lemma SAD_Icc_to_Q' (x : ℝ) (a r b : ℕ) (ha : 1 ≤ a) (hb : b + 1 = a + r) :
    ∏ t ∈ Icc a b, (x + (t : ℝ) + 1) = SADQ (x + a + 1) r := by
  have := SAD_Icc_to_Q (x + 1) a r b ha hb
  rw [← show x + 1 + (a : ℝ) = x + a + 1 by ring] 
  rw [← this]
  apply Finset.prod_congr rfl
  intro t _
  ring

lemma tred_inner (n k i j s s' : ℕ) (hi : 1 ≤ i) (hij : i < j) (hjn : j < n) (hss : s ≤ s') :
    innerFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) / (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) *
        ((∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) -
          ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
            (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) *
            ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t)) := by
  unfold innerFormula
  rw [coeffC, if_pos hss]
  have hs'1 : (0 : ℝ) < (s' : ℝ) + 1 := by positivity
  have hs'2 : (0 : ℝ) < (s' : ℝ) + 2 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hkj : (0 : ℝ) < (k : ℝ) + j + 1 := by positivity
  -- products
  have a1 : ∏ t ∈ Icc 1 (j - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + 1) (j - 1) / SADQ ((k : ℝ) + 2) (j - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) 1 (j - 1) (j - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (j - 1) (j - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have a2 : ∏ t ∈ Icc j (n - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + j) (n - j) / SADQ ((k : ℝ) + j + 1) (n - j) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) j (n - j) (n - 1) (by omega) (by omega),
      SAD_Icc_to_Q' (k : ℝ) j (n - j) (n - 1) (by omega) (by omega)]
  have b2 : ∏ t ∈ Icc j (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + j + 1) (n - j) :=
    SAD_Icc_to_Q' (k : ℝ) j (n - j) (n - 1) (by omega) (by omega)
  have c1 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) / ((s' : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (i - 1) / SADQ ((s' : ℝ) + 2) (i - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (s' : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have pi' : ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have ps : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) = SADQ ((s : ℝ) + 1) (i - 1) :=
    by
    have := SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)
    simpa using this
  have xx : ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) = SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - 1 - i) (n - 1) (by omega) (by omega)]
    push_cast; ring_nf
  have ssq : ∀ m : ℕ, ∏ ℓ ∈ Icc 1 (n - j - m), ((s' : ℝ) + j - 1 + ℓ) =
      SADQ ((s' : ℝ) + j) (n - j - m) := by
    intro m
    have := SAD_Icc_to_Q ((s' : ℝ) + j - 1) 1 (n - j - m) (n - j - m) le_rfl (by omega)
    rw [this]
    congr 1
    push_cast
    ring
  have hcast1 : ((j - 1 - i : ℕ) : ℝ) = (j : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp
  have hcast2 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  set Y := SADQ ((s' : ℝ) + i + 1) (j - 1 - i) with hYdef
  set Z := SADQ ((s' : ℝ) + j) (n - j) with hZdef
  have hY : SADQ ((s' : ℝ) + 1) (j - 1) = SADQ ((s' : ℝ) + 1) i * Y := by
    have := SADQ_add ((s' : ℝ) + 1) i (j - 1 - i)
    rw [show i + (j - 1 - i) = j - 1 by omega] at this
    rw [this, hYdef]
    congr 2
    ring
  have hZ : SADQ ((s' : ℝ) + i + 1) (n - 1 - i) = Y * Z := by
    have := SADQ_add ((s' : ℝ) + i + 1) (j - 1 - i) (n - j)
    rw [show j - 1 - i + (n - j) = n - 1 - i by omega] at this
    rw [this, hcast1]
    congr 2
    ring
  have hP : SADQ ((k : ℝ) + 2) (n - 1) =
      SADQ ((k : ℝ) + 2) (j - 1) * SADQ ((k : ℝ) + j + 1) (n - j) := by
    have := SADQ_add ((k : ℝ) + 2) (j - 1) (n - j)
    rw [show j - 1 + (n - j) = n - 1 by omega] at this
    rw [this, hcast2]
    congr 2
    ring
  have hD : SADQ ((s' : ℝ) + 1) i = ((s' : ℝ) + 1) * SADQ ((s' : ℝ) + 2) (i - 1) := by
    have := SADQ_succ' ((s' : ℝ) + 1) (i - 1)
    rw [show i - 1 + 1 = i by omega] at this
    rw [this]
    congr 2
    ring
  have hprod : ∀ m ∈ Icc 1 (n - j),
      ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t) = Y * SADQ ((s' : ℝ) + j) (n - j - m) := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - m - 1 - i) (n - m - 1) (by omega) (by omega)]
    have := SADQ_add ((s' : ℝ) + i + 1) (j - 1 - i) (n - j - m)
    rw [show j - 1 - i + (n - j - m) = n - m - 1 - i by omega] at this
    push_cast at this ⊢
    rw [show (s' : ℝ) + (i + 1 : ℝ) = (s' : ℝ) + i + 1 by ring, this, hcast1]
    congr 2
    ring
  have hsum : ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
        (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) * ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t) =
      Y * ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
        (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) * SADQ ((s' : ℝ) + j) (n - j - m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hprod m hm]
    ring
  rw [a1, a2, b2, c1, pi', ps, xx, hsum]
  simp only [ssq]
  rw [hY, hZ, hP, hD]
  have hYpos : 0 < SADQ ((s' : ℝ) + 2) (i - 1) := SADQ_pos _ hs'2 _
  have hp1 : 0 < SADQ ((k : ℝ) + 2) (j - 1) := SADQ_pos _ hk2 _
  have hB2 : 0 < SADQ ((k : ℝ) + j + 1) (n - j) := SADQ_pos _ hkj _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

lemma tred_top (n k i s s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hss : s ≤ s') :
    unclippedFormula n k n s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) / (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) *
        (∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t)) := by
  unfold unclippedFormula coeffA
  rw [if_pos rfl, coeffC, if_pos hss]
  have hs'1 : (0 : ℝ) < (s' : ℝ) + 1 := by positivity
  have hs'2 : (0 : ℝ) < (s' : ℝ) + 2 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have a1 : ∏ t ∈ Icc 1 (n - 1), ((s' : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s' : ℝ) + 1) (n - 1) / SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s' : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have c1 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) / ((s' : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (i - 1) / SADQ ((s' : ℝ) + 2) (i - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (s' : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have pi' : ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have ps : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) = SADQ ((s : ℝ) + 1) (i - 1) := by
    have := SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)
    simpa using this
  have xx : ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) = SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    rw [SAD_Icc_to_Q (s' : ℝ) (i + 1) (n - 1 - i) (n - 1) (by omega) (by omega)]
    push_cast; ring_nf
  have hX : SADQ ((s' : ℝ) + 1) (n - 1) =
      SADQ ((s' : ℝ) + 1) i * SADQ ((s' : ℝ) + i + 1) (n - 1 - i) := by
    have := SADQ_add ((s' : ℝ) + 1) i (n - 1 - i)
    rw [show i + (n - 1 - i) = n - 1 by omega] at this
    rw [this]
    congr 2
    ring
  have hD : SADQ ((s' : ℝ) + 1) i = ((s' : ℝ) + 1) * SADQ ((s' : ℝ) + 2) (i - 1) := by
    have := SADQ_succ' ((s' : ℝ) + 1) (i - 1)
    rw [show i - 1 + 1 = i by omega] at this
    rw [this]
    congr 2
    ring
  rw [a1, c1, pi', ps, xx, hX, hD]
  have hYpos : 0 < SADQ ((s' : ℝ) + 2) (i - 1) := SADQ_pos _ hs'2 _
  have hp1 : 0 < SADQ ((k : ℝ) + 2) (n - 1) := SADQ_pos _ hk2 _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

lemma tred_sumT (n k i s s' : ℕ) (hi : 1 ≤ i) (hin : i < n) (hss : s ≤ s') :
    ∑ j ∈ Ioc i n, unclippedFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) * T n k i s' := by
  set K : ℝ := (∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) with hK
  set X : ℝ := ∏ t ∈ Icc (i + 1) (n - 1), ((s' : ℝ) + t) with hX
  have hI : Ioc i n = insert n (Ioc i (n - 1)) := by
    ext j
    simp only [mem_Ioc, mem_insert]
    omega
  have hnI : n ∉ Ioc i (n - 1) := by
    simp only [mem_Ioc]
    omega
  rw [hI, Finset.sum_insert hnI, tred_top n k i s s' hi hin hss]
  have h1 : ∀ j ∈ Ioc i (n - 1), unclippedFormula n k j s' * coeffC s' i s =
      K * (X - ∑ m ∈ Icc 1 (n - j), ((n - j).choose m : ℝ) * (1 / (m : ℝ)) *
            (∏ ℓ ∈ Icc 1 m, ((k : ℝ) - s' + ℓ)) *
            ∏ t ∈ Icc (i + 1) (n - m - 1), ((s' : ℝ) + t)) := by
    intro j hj
    have hj' := mem_Ioc.1 hj
    unfold unclippedFormula
    rw [if_neg (by omega)]
    exact tred_inner n k i j s s' hi hj'.1 (by omega) hss
  rw [Finset.sum_congr rfl h1]
  have hIcc : Icc (i + 1) (n - 1) = Ioc i (n - 1) := by
    ext j
    simp only [mem_Icc, mem_Ioc]
    omega
  unfold T
  rw [← hX, hIcc]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, ← Finset.mul_sum]
  have hcard : ((n - 1 - i : ℕ) : ℝ) + 1 = (n : ℝ) - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  linear_combination (K * X) * hcard

theorem SAD_tred (n k i : ℕ) (hi : 1 ≤ i) (hin : i < n)
    (ih : ∀ i' : ℕ, i < i' → i' ≤ n → ∀ s' : Fin (k + 1),
      samplesUnclipped n k i' s' = unclippedFormula n k i' s')
    (s : Fin (k + 1)) :
    samplesUnclipped n k i s =
      1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), (((s : ℕ) : ℝ) + t) / ((k : ℝ) + t + 1)) -
        1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1)) *
          (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) *
          ∑ s' ∈ Icc (s : ℕ) k, T n k i s' := by
  rw [tred_unfold n k i hin s]
  have h1 : ∀ j ∈ Ioc i n, ∑ s' : Fin (k + 1), samplesUnclipped n k j s' * coeffC s' i s =
      ∑ s' : Fin (k + 1), unclippedFormula n k j s' * coeffC s' i s := by
    intro j hj
    have := mem_Ioc.1 hj
    apply Finset.sum_congr rfl
    intro s' _
    rw [ih j this.1 this.2 s']
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ j, ∑ s' : Fin (k + 1), unclippedFormula n k j s' * coeffC s' i s =
      ∑ s' ∈ Icc (s : ℕ) k, unclippedFormula n k j s' * coeffC s' i s := by
    intro j
    rw [Fin.sum_univ_eq_sum_range (fun s' => unclippedFormula n k j s' * coeffC s' i s) (k + 1)]
    symm
    apply Finset.sum_subset
    · intro x hx
      simp only [mem_Icc, mem_range] at hx ⊢
      omega
    · intro x hx hx'
      simp only [mem_Icc, mem_range, not_and, not_le] at hx hx'
      have : x < (s : ℕ) := by omega
      rw [coeffC, if_neg (by omega)]
      simp
  simp only [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ s' ∈ Icc (s : ℕ) k, ∑ j ∈ Ioc i n, unclippedFormula n k j s' * coeffC s' i s =
      (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) /
        (((k : ℝ) + 1) * ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1)) * T n k i s' :=
    fun s' hs' => tred_sumT n k i s s' hi hin (mem_Icc.1 hs').1
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum]
  unfold coeffA
  have hpi : ∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1) = 1 / ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [hpi]
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hpos : 0 < ∏ t ∈ Icc 1 (n - 1), ((k : ℝ) + t + 1) := by
    apply Finset.prod_pos
    intro t _
    positivity
  field_simp


lemma ucf_inner (n k i s : ℕ) (hi : 1 ≤ i) (hin : i < n) :
    1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), (((s : ℕ) : ℝ) + t) / ((k : ℝ) + t + 1)) -
        1 / ((k : ℝ) + 1) * (∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1)) *
          (∏ t ∈ Icc 1 (i - 1), (((s : ℕ) : ℝ) + t)) * keyRHS n k i s =
      innerFormula n k i s := by
  unfold innerFormula keyRHS
  have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hki : (0 : ℝ) < (k : ℝ) + i + 1 := by positivity
  have a1 : ∏ t ∈ Icc 1 (n - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (n - 1) / SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have a2 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s : ℝ) + 1) (i - 1) / SADQ ((k : ℝ) + 2) (i - 1) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega),
      SAD_Icc_to_Q' (k : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have a3 : ∏ t ∈ Icc i (n - 1), ((s : ℝ) + t) / ((k : ℝ) + t + 1) =
      SADQ ((s : ℝ) + i) (n - i) / SADQ ((k : ℝ) + i + 1) (n - i) := by
    rw [Finset.prod_div_distrib, SAD_Icc_to_Q (s : ℝ) i (n - i) (n - 1) hi (by omega),
      SAD_Icc_to_Q' (k : ℝ) i (n - i) (n - 1) hi (by omega)]
  have a4 : ∏ t ∈ Icc i (n - 1), ((k : ℝ) + t + 1) = SADQ ((k : ℝ) + i + 1) (n - i) :=
    SAD_Icc_to_Q' (k : ℝ) i (n - i) (n - 1) hi (by omega)
  have a5 : ∏ t ∈ Icc 1 (n - 1), 1 / ((k : ℝ) + t + 1) = 1 / SADQ ((k : ℝ) + 2) (n - 1) := by
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const_one]
    rw [SAD_Icc_to_Q' (k : ℝ) 1 (n - 1) (n - 1) le_rfl (by omega)]
    norm_num
    ring_nf
  have a6 : ∏ t ∈ Icc 1 (i - 1), ((s : ℝ) + t) = SADQ ((s : ℝ) + 1) (i - 1) := by
    have := SAD_Icc_to_Q (s : ℝ) 1 (i - 1) (i - 1) le_rfl (by omega)
    simpa using this
  have hS : ∀ j ∈ Icc 1 (n - i), ∏ ℓ ∈ Icc 1 (n - i - j), ((s : ℝ) + i - 1 + ℓ) =
      ∏ t ∈ Icc i (n - j - 1), ((s : ℝ) + t) := by
    intro j hj
    have hj' := mem_Icc.1 hj
    have e1 := SAD_Icc_to_Q ((s : ℝ) + i - 1) 1 (n - i - j) (n - i - j) le_rfl (by omega)
    have e2 := SAD_Icc_to_Q (s : ℝ) i (n - i - j) (n - j - 1) hi (by omega)
    rw [e1, e2]
    congr 1
    push_cast
    ring
  have hsum : ∑ j ∈ Icc 1 (n - i), ((n - i).choose j : ℝ) * (1 / (j : ℝ)) *
        (∏ ℓ ∈ Icc 1 j, ((k : ℝ) - s + ℓ)) * ∏ ℓ ∈ Icc 1 (n - i - j), ((s : ℝ) + i - 1 + ℓ) =
      ∑ j ∈ Icc 1 (n - i), ((n - i).choose j : ℝ) * (1 / (j : ℝ)) *
        (∏ ℓ ∈ Icc 1 j, ((k : ℝ) - s + ℓ)) * ∏ t ∈ Icc i (n - j - 1), ((s : ℝ) + t) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hS j hj]
  rw [hsum, a1, a2, a3, a4, a5, a6]
  have hX : SADQ ((s : ℝ) + 1) (n - 1) =
      SADQ ((s : ℝ) + 1) (i - 1) * SADQ ((s : ℝ) + i) (n - i) := by
    have := SADQ_add ((s : ℝ) + 1) (i - 1) (n - i)
    rw [show i - 1 + (n - i) = n - 1 by omega] at this
    rw [this]
    congr 2
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hP : SADQ ((k : ℝ) + 2) (n - 1) =
      SADQ ((k : ℝ) + 2) (i - 1) * SADQ ((k : ℝ) + i + 1) (n - i) := by
    have := SADQ_add ((k : ℝ) + 2) (i - 1) (n - i)
    rw [show i - 1 + (n - i) = n - 1 by omega] at this
    rw [this]
    congr 2
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hX, hP]
  have h1 : 0 < SADQ ((k : ℝ) + 2) (i - 1) := SADQ_pos _ hk2 _
  have h2 : 0 < SADQ ((k : ℝ) + i + 1) (n - i) := SADQ_pos _ hki _
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

theorem solution (n k i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Fin (k + 1)) :
    samplesUnclipped n k i s = unclippedFormula n k i s := by
  suffices H : ∀ d : ℕ, ∀ i : ℕ, n - i = d → 1 ≤ i → i ≤ n → ∀ s : Fin (k + 1),
      samplesUnclipped n k i s = unclippedFormula n k i s from H (n - i) i rfl hi hin s
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro i hd hi hin s
    by_cases hlt : i < n
    · have ih : ∀ i' : ℕ, i < i' → i' ≤ n → ∀ s' : Fin (k + 1),
          samplesUnclipped n k i' s' = unclippedFormula n k i' s' := by
        intro i' h1 h2 s'
        exact ihd (n - i') (by omega) i' rfl (by omega) h2 s'
      rw [SAD_tred n k i hi hlt ih s]
      have hkey := SAD_keyid n k i (s : ℕ) hi hlt (by have := s.isLt; omega)
      rw [hkey]
      unfold unclippedFormula
      rw [if_neg (by omega)]
      exact ucf_inner n k i (s : ℕ) hi hlt
    · have : i = n := by omega
      subst this
      unfold samplesUnclipped unclippedFormula
      rw [unclippedDual, if_neg (lt_irrefl _), if_pos rfl]
