-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_expComp_gap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:22:28.656827+00:00
-- url     : https://prove2.me/submissions/179c4cb9-aec1-4189-a92a-d2a603d04519

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries Finset
noncomputable section
variable {K : Type*} [Field K]

theorem solution [CharZero K] (Ω : K) (lg : PowerSeries K) (M : ℕ) (hM : 2 ≤ M)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0) :
    coeff M (expComp Ω lg) = Ω * coeff M lg + Ω ^ M / (M.factorial : K) := by
  have hsupp {k : ℕ} (hk1 : k ≠ 1) (hkM : k < M) : coeff k lg = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact hl0
    · have : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hk1.symm)
      exact hlg k this hkM
  have hpow : ∀ n, 1 ≤ n → ∀ m, m < n + (M - 1) →
      coeff m (lg ^ n) = if m = n then (1 : K) else 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro m hm
      have hM1 : 1 ≤ M := le_trans (by decide : (1 : ℕ) ≤ 2) hM
      have hmM : m < M := by
        rw [Nat.add_comm, Nat.sub_add_cancel hM1] at hm
        exact hm
      rw [pow_one]
      split_ifs with h
      · rw [h, hl1]
      · exact hsupp h hmM
    | succ n hn ih =>
      intro m hm
      rw [pow_succ, coeff_mul]
      by_cases hm' : m = n + 1
      · subst hm'
        rw [if_pos rfl, sum_eq_single (n, 1)]
        · have hnlt : n < n + (M - 1) := Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt (by
            exact lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hM))
          rw [ih n hnlt, if_pos rfl, hl1, mul_one]
        · intro p hp hne
          rw [HasAntidiagonal.mem_antidiagonal] at hp
          by_cases hj1 : p.2 = 1
          · have : p.1 = n := by
              have := congrArg (fun t => t - 1) hp
              -- p.1 + p.2 = n+1, p.2=1
              omega
            exact (hne (Prod.ext this hj1)).elim
          · by_cases hjM : p.2 < M
            · rw [hsupp hj1 hjM, mul_zero]
            · have hp1 : p.1 < n := by omega
              have hp1' : p.1 < n + (M - 1) := Nat.lt_of_lt_of_le hp1 (Nat.le_add_right _ _)
              have hne' : p.1 ≠ n := ne_of_lt hp1
              rw [ih p.1 hp1', if_neg hne', zero_mul]
        · intro hnot
          exact (hnot (by simp [HasAntidiagonal.mem_antidiagonal])).elim
      · rw [if_neg hm']
        apply sum_eq_zero
        intro p hp
        rw [HasAntidiagonal.mem_antidiagonal] at hp
        by_cases hj1 : p.2 = 1
        · have hp1 : p.1 < n + (M - 1) := by omega
          have hne : p.1 ≠ n := by omega
          rw [ih p.1 hp1, if_neg hne, zero_mul]
        · by_cases hjM : p.2 < M
          · rw [hsupp hj1 hjM, mul_zero]
          · have hp1 : p.1 < n := by omega
            have hp1' : p.1 < n + (M - 1) := Nat.lt_of_lt_of_le hp1 (Nat.le_add_right _ _)
            have hne : p.1 ≠ n := ne_of_lt hp1
            rw [ih p.1 hp1', if_neg hne, zero_mul]
  rw [expComp, coeff_mk]
  rw [sum_range_succ]
  have hMpow : coeff M (lg ^ M) = 1 := by
    have hn1 : 1 ≤ M := le_trans (by decide : (1 : ℕ) ≤ 2) hM
    have hm : M < M + (M - 1) := Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt (Nat.succ_le_iff.mp hM))
    rw [hpow M hn1 M hm, if_pos rfl]
  have hfront :
      ∑ n ∈ range M, Ω ^ n / (n.factorial : K) * coeff M (lg ^ n) = Ω * coeff M lg := by
    rw [sum_eq_single 1]
    · simp
    · intro n hn hne
      rw [mem_range] at hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp [PowerSeries.coeff_one, (show M ≠ 0 from ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hM))]
      · have hn2 : 2 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hpos) hne.symm)
        have hn1 : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn2
        have hm : M < n + (M - 1) := by omega
        have hneM : (M : ℕ) ≠ n := ne_of_gt hn
        rw [hpow n hn1 M hm, if_neg hneM, mul_zero]
    · intro hnot
      exact (hnot (by simp [mem_range]; omega)).elim
  rw [hfront, hMpow, mul_one]
