-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.coeff_subst_gap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:25:52.912873+00:00
-- url     : https://prove2.me/submissions/7f5d1150-727b-4bd8-9b22-25a6a61848e6

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

theorem solution (lg P : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (b : K)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1) (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → coeff j P = 0) :
    coeff M (subst P lg) = coeff M P + coeff M lg * b ^ M := by
  have hPsupp {k : ℕ} (hk1 : k ≠ 1) (hkM : k < M) : coeff k P = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact hP0
    · have : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hk1.symm)
      exact hPg k this hkM
  have hpow : ∀ n, 1 ≤ n → ∀ m, m < n + (M - 1) →
      coeff m (P ^ n) = if m = n then b ^ n else 0 := by
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
      · rw [h, hP1, pow_one]
      · exact hPsupp h hmM
    | succ n hn ih =>
      intro m hm
      rw [pow_succ, coeff_mul]
      by_cases hm' : m = n + 1
      · subst hm'
        rw [if_pos rfl, sum_eq_single (n, 1)]
        · have hnlt : n < n + (M - 1) :=
            Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hM))
          rw [ih n hnlt, if_pos rfl, hP1, pow_succ, mul_comm]
        · intro p hp hne
          rw [HasAntidiagonal.mem_antidiagonal] at hp
          by_cases hj1 : p.2 = 1
          · have : p.1 = n := by omega
            exact (hne (Prod.ext this hj1)).elim
          · by_cases hjM : p.2 < M
            · rw [hPsupp hj1 hjM, mul_zero]
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
          · rw [hPsupp hj1 hjM, mul_zero]
          · have hp1 : p.1 < n := by omega
            have hp1' : p.1 < n + (M - 1) := Nat.lt_of_lt_of_le hp1 (Nat.le_add_right _ _)
            have hne : p.1 ≠ n := ne_of_lt hp1
            rw [ih p.1 hp1', if_neg hne, zero_mul]
  have hP : HasSubst P :=
    HasSubst.of_constantCoeff_zero' (by rwa [← coeff_zero_eq_constantCoeff])
  rw [coeff_subst' hP]
  have hterm (d : ℕ) :
      coeff d lg • coeff M (P ^ d) =
        if d = 1 then coeff M P
        else if d = M then coeff M lg * b ^ M else 0 := by
    by_cases hd1 : d = 1
    · subst hd1
      simp [hl1]
    · by_cases hdM : d = M
      · have hn1 : 1 ≤ M := le_trans (by decide : (1 : ℕ) ≤ 2) hM
        have hm : M < M + (M - 1) :=
          Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hM))
        rw [if_neg hd1, if_pos hdM, hdM, hpow M hn1 M hm, if_pos rfl, smul_eq_mul]
      · rw [if_neg hd1, if_neg hdM]
        by_cases hd0 : d = 0
        · subst hd0
          simp [hl0]
        · by_cases hdlt : d < M
          · have hd2 : 2 ≤ d := by omega
            rw [hlg d hd2 hdlt, zero_smul]
          · have hdgt : M < d := Nat.lt_of_le_of_ne (le_of_not_gt hdlt) (Ne.symm hdM)
            have : coeff M (P ^ d) = 0 := by
              have hn1 : 1 ≤ d := le_trans (by decide : (1 : ℕ) ≤ 2)
                (Nat.succ_le_of_lt (lt_of_lt_of_le (Nat.succ_le_iff.mp hM) (le_of_lt hdgt)))
              -- M < d so M < d + (M-1) and M ≠ d
              have hm : M < d + (M - 1) := Nat.lt_of_lt_of_le hdgt (Nat.le_add_right _ _)
              rw [hpow d hn1 M hm, if_neg (ne_of_lt hdgt)]
            rw [this, smul_zero]
  simp_rw [hterm]
  have hne : (1 : ℕ) ≠ M := ne_of_lt (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hM)
  have hsuppF :
      (Function.support fun d : ℕ =>
          if d = 1 then coeff M P else if d = M then coeff M lg * b ^ M else 0) ⊆
        ({1, M} : Finset ℕ) := by
    intro d hd
    have hd0 : (if d = 1 then coeff M P else if d = M then coeff M lg * b ^ M else 0) ≠ 0 := hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    split_ifs at hd0 with h1 hMd
    · exact Or.inl h1
    · exact Or.inr hMd
    · exact (hd0 rfl).elim
  rw [finsum_eq_sum_of_support_subset _ hsuppF, Finset.sum_pair hne]
  simp [hne, hne.symm]
