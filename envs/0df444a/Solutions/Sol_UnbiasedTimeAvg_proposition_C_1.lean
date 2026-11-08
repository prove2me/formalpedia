-- Prove2me | solution 1 for UnbiasedTimeAvg.proposition_C_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:03:26.575916+00:00
-- url     : https://prove2.me/submissions/fa7e6f15-c22c-451c-bd12-1efa01099981

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_A1Sequence
import Definitions.Def_UnbiasedTimeAvg_nuBar

namespace Aux_UTAC1

open UnbiasedTimeAvg

noncomputable def s (ν : ℕ → ℝ) (k : ℕ) : ℝ := Real.sqrt (ν k / ((k : ℝ) + 1))

theorem s_nonneg (ν : ℕ → ℝ) (k : ℕ) : 0 ≤ s ν k := Real.sqrt_nonneg _

theorem s_anti {ν : ℕ → ℝ} (hν : A1Sequence ν) {k m : ℕ} (hkm : k ≤ m) : s ν m ≤ s ν k := by
  unfold s
  apply Real.sqrt_le_sqrt
  have h1 : ν m ≤ ν k := hν.antitone hkm
  have h2 : (0 : ℝ) ≤ ν k := (hν.pos k).le
  have h3 : ((k : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  calc ν m / ((m : ℝ) + 1) ≤ ν k / ((m : ℝ) + 1) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ ν k / ((k : ℝ) + 1) := div_le_div_of_nonneg_left h2 (by positivity) h3

theorem nu_eq {ν : ℕ → ℝ} (hν : A1Sequence ν) (k : ℕ) : ν k = ((k : ℝ) + 1) * s ν k ^ 2 := by
  unfold s
  rw [Real.sq_sqrt (div_nonneg (hν.pos k).le (by positivity))]
  field_simp

theorem main {ν : ℕ → ℝ} (hν : A1Sequence ν) (h : ℕ) : ∀ m : ℕ,
    ∑ i ∈ Finset.Icc (2 * h) m, ν i ≤ (∑ k ∈ Finset.Icc h m, s ν k) ^ 2 := by
  intro m
  induction m with
  | zero =>
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      simp only [mul_zero, Finset.Icc_self, Finset.sum_singleton]
      rw [nu_eq hν 0]
      simp
    · have : Finset.Icc (2 * h) 0 = ∅ := by
        ext x; simp; omega
      rw [this, Finset.sum_empty]
      positivity
  | succ m ih =>
    by_cases hm : m + 1 < h
    · have e1 : Finset.Icc (2 * h) (m + 1) = ∅ := by ext x; simp; omega
      rw [e1, Finset.sum_empty]
      positivity
    · push_neg at hm
      rw [Finset.sum_Icc_succ_top hm]
      set P := ∑ k ∈ Finset.Icc h m, s ν k with hP
      have hP0 : 0 ≤ P := Finset.sum_nonneg (fun k _ => s_nonneg ν k)
      have hPge : ((m + 1 - h : ℕ) : ℝ) * s ν (m + 1) ≤ P := by
        have : ∑ _k ∈ Finset.Icc h m, s ν (m + 1) ≤ P := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Icc] at hk
          exact s_anti hν (by omega)
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
        exact this
      have hcast : ((m + 1 - h : ℕ) : ℝ) = (m : ℝ) + 1 - h := by
        rw [Nat.cast_sub hm]; push_cast; ring
      rw [hcast] at hPge
      have hs0 := s_nonneg ν (m + 1)
      have hexp : (P + s ν (m + 1)) ^ 2 ≥
          P ^ 2 + (2 * ((m : ℝ) + 1 - h) + 1) * s ν (m + 1) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right hPge hs0]
      by_cases h2 : 2 * h ≤ m + 1
      · rw [Finset.sum_Icc_succ_top h2]
        have hnu := nu_eq hν (m + 1)
        have hhR : (2 * h : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h2
        have : ν (m + 1) ≤ (2 * ((m : ℝ) + 1 - h) + 1) * s ν (m + 1) ^ 2 := by
          rw [hnu]
          push_cast
          have := sq_nonneg (s ν (m + 1))
          nlinarith
        linarith
      · push_neg at h2
        have e1 : Finset.Icc (2 * h) (m + 1) = Finset.Icc (2 * h) m := by
          ext x; simp; omega
        rw [e1]
        have : 0 ≤ (2 * ((m : ℝ) + 1 - h) + 1) * s ν (m + 1) ^ 2 := by
          have hhR : (h : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hm
          have := sq_nonneg (s ν (m + 1))
          nlinarith
        linarith

end Aux_UTAC1

open UnbiasedTimeAvg Aux_UTAC1 in
theorem solution {ν : ℕ → ℝ} (hν : A1Sequence ν) (h h' : ℕ) (hh : 2 * h ≤ h') :
    ∑ i ∈ Finset.Icc (2 * h) h', ν i ≤ (nuBar ν h) ^ 2 := by
  have h1 := main hν h h'
  have hsum : Summable (fun i => s ν (i + h)) :=
    (summable_nat_add_iff h).mpr hν.summable_sqrt
  have hP : ∑ k ∈ Finset.Icc h h', s ν k ≤ nuBar ν h := by
    have e : ∑ k ∈ Finset.Icc h h', s ν k = ∑ i ∈ Finset.range (h' + 1 - h), s ν (i + h) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (c := h)]
      congr 1
      ext x; simp; omega
    rw [e]
    unfold nuBar
    exact hsum.sum_le_tsum _ (fun i _ => s_nonneg ν _)
  have hP0 : 0 ≤ ∑ k ∈ Finset.Icc h h', s ν k := Finset.sum_nonneg (fun k _ => s_nonneg ν k)
  calc ∑ i ∈ Finset.Icc (2 * h) h', ν i ≤ (∑ k ∈ Finset.Icc h h', s ν k) ^ 2 := h1
    _ ≤ (nuBar ν h) ^ 2 := pow_le_pow_left₀ hP0 hP 2
