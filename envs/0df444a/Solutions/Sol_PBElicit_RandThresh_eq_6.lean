-- Prove2me | solution 1 for PBElicit.RandThresh.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:45:44.455003+00:00
-- url     : https://prove2.me/submissions/045bed74-8f86-46ef-bd1e-60d35cdd0ac9

import Mathlib
import Definitions.Def_PBElicit_RandThresh_Setting

open Classical PBElicit.RandThresh

lemma pb6_dyad (L : ℕ) (y : ℝ) (h1 : 1 < y) (h2 : y ≤ 2 ^ L) :
    ∃ j ∈ Finset.Icc 1 L, (2:ℝ) ^ (j - 1) < y ∧ y ≤ 2 ^ j := by
  induction L with
  | zero => simp at h2; linarith
  | succ L ih =>
    by_cases h : y ≤ 2 ^ L
    · obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, by simp only [Finset.mem_Icc] at hj ⊢; omega, hj'⟩
    · exact ⟨L + 1, by simp, by simpa using (not_le.mp h), h2⟩

lemma pb6_mem_ivl (m j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    x ∈ Ivl m j ↔ lo m j < x ∧ x ≤ up m j := by
  have : j ≠ 0 := by omega
  simp [Ivl, this]

lemma pb6_cover (m K : ℕ) (hmK : m = 2 ^ K) (x : ℝ) (hx1 : 1 / (m:ℝ)^2 < x) (hx2 : x ≤ 1) :
    ∃ j ∈ Finset.Icc 1 (2 * K), x ∈ Ivl m j := by
  have hm2 : (m:ℝ)^2 = 2 ^ (2 * K) := by rw [hmK]; push_cast; rw [← pow_mul, mul_comm]
  have hmpos : (0:ℝ) < (m:ℝ)^2 := by rw [hm2]; positivity
  obtain ⟨j, hj, h1, h2⟩ := pb6_dyad (2 * K) (x * (m:ℝ)^2)
    (by rw [div_lt_iff₀ hmpos] at hx1; linarith)
    (by rw [← hm2]; nlinarith)
  refine ⟨j, hj, ?_⟩
  rw [pb6_mem_ivl m j (Finset.mem_Icc.mp hj).1]
  have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
  simp only [lo, up, hj1, if_false]
  constructor
  · rw [div_lt_iff₀ hmpos]; exact h1
  · rw [le_div_iff₀ hmpos]; exact h2

lemma pb6_disj (m j j' : ℕ) (hm : 0 < m) (hj : 1 ≤ j) (hjj : j < j') (x : ℝ)
    (h : x ∈ Ivl m j) (h' : x ∈ Ivl m j') : False := by
  rw [pb6_mem_ivl m j hj] at h
  rw [pb6_mem_ivl m j' (by omega)] at h'
  have hj1 : j' ≠ 0 := by omega
  have : up m j ≤ lo m j' := by
    simp only [up, lo, hj1, if_false]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith [h.2, h'.1]

lemma pb6_voter (m K : ℕ) (hmK : m = 2 ^ K) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∑ j ∈ Finset.Icc 1 (2 * K), (if x ∈ Ivl m j then 1 else 0) * lo m j ≤ x ∧
      x ≤ 1 / (m:ℝ)^2 + ∑ j ∈ Finset.Icc 1 (2 * K), (if x ∈ Ivl m j then 1 else 0) * up m j := by
  have hm : 0 < m := by rw [hmK]; positivity
  have hup : ∀ j, 0 ≤ up m j := fun j => by unfold up; positivity
  have hlo : ∀ j, 0 ≤ lo m j := fun j => by unfold lo; split_ifs <;> positivity
  constructor
  · by_cases hex : ∃ j ∈ Finset.Icc 1 (2 * K), x ∈ Ivl m j
    · obtain ⟨j0, hj0, hx⟩ := hex
      rw [Finset.sum_eq_single_of_mem j0 hj0]
      · rw [if_pos hx, one_mul]
        exact le_of_lt ((pb6_mem_ivl m j0 (Finset.mem_Icc.mp hj0).1 x).mp hx).1
      · intro j hj hne
        rw [if_neg, zero_mul]
        intro hx'
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact pb6_disj m j j0 hm (Finset.mem_Icc.mp hj).1 hlt x hx' hx
        · exact pb6_disj m j0 j hm (Finset.mem_Icc.mp hj0).1 hgt x hx hx'
    · push_neg at hex
      rw [Finset.sum_eq_zero (fun j hj => by rw [if_neg (hex j hj), zero_mul])]
      exact hx0
  · have hs : 0 ≤ ∑ j ∈ Finset.Icc 1 (2 * K), (if x ∈ Ivl m j then 1 else 0) * up m j :=
      Finset.sum_nonneg (fun j _ => by split_ifs <;> simp [hup])
    by_cases hsmall : x ≤ 1 / (m:ℝ)^2
    · linarith
    · obtain ⟨j0, hj0, hx⟩ := pb6_cover m K hmK x (not_le.mp hsmall) hx1
      have := Finset.single_le_sum (f := fun j => (if x ∈ Ivl m j then (1:ℝ) else 0) * up m j)
        (fun j _ => by split_ifs <;> simp [hup]) hj0
      simp only [if_pos hx, one_mul] at this
      have hx' := ((pb6_mem_ivl m j0 (Finset.mem_Icc.mp hj0).1 x).mp hx).2
      have : (0:ℝ) ≤ 1 / (m:ℝ)^2 := by positivity
      linarith

lemma pb6_cnt {n : ℕ} {A : Type*} (v : Fin n → A → ℝ) (m : ℕ) (a : A) (j : ℕ) :
    (cnt v m a j : ℝ) = ∑ i, (if v i a ∈ Ivl m j then 1 else 0) := by
  unfold cnt
  rw [Finset.natCast_card_filter]

theorem solution {n : ℕ} {A : Type*} [Fintype A] (v : Fin n → A → ℝ) (hv : IsUtilityProfile v)
    (m K : ℕ) (hA : Fintype.card A = m) (hmK : m = 2 ^ K) (a : A) :
    ∑ j ∈ Finset.Icc 1 (2 * K), (cnt v m a j : ℝ) * lo m j ≤ ∑ i, v i a ∧
      ∑ i, v i a ≤ (n : ℝ) / (m : ℝ) ^ 2 + ∑ j ∈ Finset.Icc 1 (2 * K), (cnt v m a j : ℝ) * up m j := by
  have hle1 : ∀ i, v i a ≤ 1 := by
    intro i
    rw [← hv.2 i]
    exact Finset.single_le_sum (f := fun b => v i b) (fun b _ => hv.1 i b) (Finset.mem_univ a)
  have key := fun i => pb6_voter m K hmK (v i a) (hv.1 i a) (hle1 i)
  simp only [pb6_cnt, Finset.sum_mul]
  constructor
  · rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ => (key i).1)
  · rw [Finset.sum_comm (s := Finset.Icc 1 (2 * K))]
    have : (n:ℝ) / (m:ℝ)^2 = ∑ _i : Fin n, 1 / (m:ℝ)^2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_one_div]
    rw [this, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => (key i).2)
