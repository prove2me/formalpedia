-- Prove2me | solution 1 for TaoFivePrimes.prime_in_short_interval_above_exp301
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T17:51:35.073159+00:00
-- url     : https://prove2.me/submissions/58499ba7-f61a-49ed-af04-64e1c14237c8

import Mathlib
import Theorems.Thm_TaoFivePrimes_dusart_table1_psi_bounds_for_log_four_above_exp300
import Theorems.Thm_RamareSaouter2003_prime_interval_finite_range

/-!
# Short prime intervals from quantitative Chebyshev estimates

The final target is Tao's interval of relative width `1/28000000` for every
`x ≥ 11000000000`. These lemmas isolate the independent analytic argument.
They do not use either of the circular Ramaré--Saouter platform reductions.
-/

open scoped BigOperators

namespace ShortPrimeIntervals

/-- A strict increase of theta supplies a prime, including endpoint conventions. -/
theorem prime_of_theta_lt (x y : ℝ) (hy0 : 0 ≤ y) (hyx : y ≤ x)
    (h : Chebyshev.theta y < Chebyshev.theta x) :
    ∃ p : ℕ, p.Prime ∧ y < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  classical
  by_contra hex
  have hnone : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → (p : ℝ) ≤ y := by
    intro p hp hpx
    by_contra! hpy
    exact hex ⟨p, hp, hpy, hpx⟩
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hsets : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    ext p
    rw [Nat.mem_primesLE, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpx, hp⟩
      exact ⟨Nat.le_floor (hnone p hp ((Nat.le_floor_iff hx0).mp hpx)), hp⟩
    · rintro ⟨hpy, hp⟩
      exact ⟨le_trans hpy (Nat.floor_le_floor hyx), hp⟩
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, hsets] at h
  exact (lt_irrefl _) h

/-- The target interval follows from two explicit psi bounds and the standard
prime-power correction. The hypotheses will be supplied by proved estimates. -/
theorem prime_of_psi_bounds (x : ℝ) (hx : 1 ≤ x)
    (hleft : |Chebyshev.psi (x * (1 - 1 / 28000000)) -
        x * (1 - 1 / 28000000)| ≤
      (1225 / (10 : ℝ)^11) * (x * (1 - 1 / 28000000)))
    (hright : |Chebyshev.psi x - x| ≤ (1225 / (10 : ℝ)^11) * x)
    (hpower : 2 * Real.sqrt x * Real.log x ≤ x / (10 : ℝ)^8) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28000000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hy0 : 0 ≤ x * (1 - 1 / 28000000) := mul_nonneg hx0.le (by norm_num)
  have hyx : x * (1 - 1 / 28000000) ≤ x := by nlinarith only [hx0]
  apply prime_of_theta_lt x (x * (1 - 1 / 28000000)) hy0 hyx
  have hl := (abs_le.mp hright).1
  have hu := (abs_le.mp hleft).2
  have hp := Chebyshev.psi_sub_theta_le hx
  have ht := Chebyshev.theta_le_psi (x * (1 - 1 / 28000000))
  norm_num at hl hu hpower
  nlinarith only [hl, hu, hp, ht, hpower, hx0]

/-- The standard prime-power correction fits the remaining numerical margin
already at `10^20`. The logarithm estimate is uniform on the whole half-line. -/
theorem prime_power_error_above_1e20 (x : ℝ) (hx : (10 : ℝ)^20 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤ x / (10 : ℝ)^8 := by
  have hx0 : 0 < x := by norm_num at hx; linarith only [hx]
  have hsquare := Real.sq_sqrt hx0.le
  have hroot : (10 : ℝ)^10 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hx ⊢
    exact hx
  have hlog10 : Real.log 10 ≤ (12 / 5 : ℝ) := by
    have he : (8 / 3 : ℝ) < Real.exp 1 := by
      linarith only [Real.exp_one_gt_d9]
    have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 8 / 3)
      (by norm_num : (12 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    have h12 : (10 : ℝ)^5 < Real.exp 12 := lt_trans (by norm_num) hp
    have hscale : Real.exp (12 / 5 : ℝ)^5 = Real.exp 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hsmall : (10 : ℝ) < Real.exp (12 / 5 : ℝ) := by
      apply (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 10)
        (Real.exp_pos _).le (by norm_num : (5 : ℕ) ≠ 0)).mp
      rwa [hscale]
    exact (Real.log_lt_iff_lt_exp (by norm_num)).mpr hsmall |>.le
  have hdiv := Real.log_le_sub_one_of_pos
    (div_pos (Real.sqrt_pos.2 hx0) (by norm_num : (0 : ℝ) < 10^10))
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0.le,
    Real.log_pow] at hdiv
  have hlogroot : (2 * (10 : ℝ)^8) * Real.log x ≤ Real.sqrt x := by
    norm_num at hdiv hroot ⊢
    linarith only [hdiv, hroot, hlog10]
  have hmul := mul_le_mul_of_nonneg_left hlogroot (Real.sqrt_nonneg x)
  nlinarith only [hmul, hsquare]

/-- The elementary prime-power correction is negligible throughout the analytic
tail. The proof uses an exponential tangent bound, not numerical sampling. -/
theorem prime_power_error_of_log_ge_300 (x : ℝ) (hx : 0 < x)
    (hlog : 300 ≤ Real.log x) :
    2 * Real.sqrt x * Real.log x ≤ x / (10 : ℝ)^10 := by
  have hexp150 : (10 : ℝ)^20 ≤ Real.exp 150 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      Real.exp_one_gt_two.le 150
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith only [h]
  have hhalf : 0 ≤ 1 + (Real.log x - 300) / 2 := by linarith only [hlog]
  have htangent : 1 + (Real.log x - 300) / 2 ≤
      Real.exp ((Real.log x - 300) / 2) := by
    simpa only [add_comm] using Real.add_one_le_exp ((Real.log x - 300) / 2)
  have hroot : (2 * (10 : ℝ)^10) * Real.log x ≤ Real.sqrt x := by
    calc
      (2 * (10 : ℝ)^10) * Real.log x ≤
          (10 : ℝ)^20 * (1 + (Real.log x - 300) / 2) := by
        nlinarith only [hlog]
      _ ≤ Real.exp 150 * Real.exp ((Real.log x - 300) / 2) :=
        mul_le_mul hexp150 htangent hhalf (Real.exp_pos 150).le
      _ = Real.exp (Real.log x / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.sqrt x := by rw [Real.exp_half, Real.exp_log hx]
  have hmul := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg x)
  have hsq := Real.sq_sqrt hx.le
  nlinarith only [hmul, hsq]

/-- An already proved common Dusart tail, specialized to the constant needed
for the target interval. No numerical RH hypothesis is assumed here. -/
theorem psi_error_above_exp300 (x : ℝ) (hx : Real.exp 300 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1225 / (10 : ℝ)^11) * x := by
  let r : DusartThetaTable.Row := ⟨45, 50, 1225 / 10^11⟩
  have hr : r ∈ DusartThetaTable.rows := by
    norm_num [r, DusartThetaTable.rows]
  have h45 : Real.exp 45 ≤ x :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  have h := TaoFivePrimes.dusart_table1_psi_bounds_for_log_four_above_exp300 r hr x h45 hx
  norm_num [r] at h ⊢
  exact h

/-- The full infinite tail of the short-prime-interval target. -/
theorem prime_interval_above_exp301 (x : ℝ) (hx : Real.exp 301 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28000000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  have he300 : 0 < Real.exp 300 := Real.exp_pos _
  have hdouble : 2 * Real.exp 300 ≤ x := by
    calc
      2 * Real.exp 300 ≤ Real.exp 1 * Real.exp 300 :=
        mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le he300.le
      _ = Real.exp 301 := by rw [← Real.exp_add]; norm_num
      _ ≤ x := hx
  have hx300 : Real.exp 300 ≤ x := by linarith only [hdouble, he300]
  have hy300 : Real.exp 300 ≤ x * (1 - 1 / 28000000) := by
    nlinarith only [hdouble, he300]
  have hx1 : 1 ≤ x := by
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp 300 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ x := hx300
  have hx0 : 0 < x := by linarith only [hx1]
  have hlog : 300 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx300
  exact prime_of_psi_bounds x hx1
    (psi_error_above_exp300 _ hy300) (psi_error_above_exp300 x hx300)
    ((prime_power_error_of_log_ge_300 x hx0 hlog).trans (by
      norm_num
      nlinarith only [hx0]))

/-- The endpoint estimate needed by the independent middle-range route. -/
theorem prime_interval_of_middle_estimate (x : ℝ) (hx : (10 : ℝ)^20 ≤ x)
    (hleft : |Chebyshev.psi (x * (1 - 1 / 28000000)) -
        x * (1 - 1 / 28000000)| ≤
      (1225 / (10 : ℝ)^11) * (x * (1 - 1 / 28000000)))
    (hright : |Chebyshev.psi x - x| ≤ (1225 / (10 : ℝ)^11) * x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28000000) < (p : ℝ) ∧ (p : ℝ) ≤ x := by
  have hx1 : 1 ≤ x := by norm_num at hx; linarith only [hx]
  exact prime_of_psi_bounds x hx1 hleft hright (prime_power_error_above_1e20 x hx)

/-- The complete Tao branch follows from one independent middle-range estimate.
This is a conditional reduction, not a proof that its hypothesis holds. Both
the previously proved finite range and the new infinite tail are included. -/
theorem full_branch_of_middle_psi
    (hmid : ∀ y : ℝ, Real.exp 45 ≤ y → y ≤ Real.exp 301 →
      |Chebyshev.psi y - y| ≤ (1225 / (10 : ℝ)^11) * y)
    (x : ℝ) (hx : 1.1 * 10^10 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x - p ≤ x / (2.8 * 10^7) := by
  have hx0 : 0 < x := by norm_num at hx; linarith only [hx]
  by_cases hfinite : x < (10 : ℝ)^20
  · obtain ⟨p, hp, hlow, hupp⟩ := RamareSaouter2003.prime_interval_finite_range x
      (by norm_num at hx ⊢; linarith only [hx]) hfinite
    refine ⟨p, hp, hupp, ?_⟩
    have hgap : x - (p : ℝ) < x / 28314000 := by linarith only [hlow]
    have hfrac : x / 28314000 ≤ x / 28000000 :=
      div_le_div_of_nonneg_left hx0.le (by norm_num) (by norm_num)
    norm_num
    linarith only [hgap, hfrac]
  · have hx20 : (10 : ℝ)^20 ≤ x := le_of_not_gt hfinite
    by_cases htail : Real.exp 301 ≤ x
    · obtain ⟨p, hp, hlow, hupp⟩ := prime_interval_above_exp301 x htail
      refine ⟨p, hp, hupp, ?_⟩
      norm_num
      linarith only [hlow]
    · have h301 : x ≤ Real.exp 301 := (lt_of_not_ge htail).le
      have he45 : Real.exp 45 ≤ (10 : ℝ)^20 * (1 - 1 / 28000000) := by
        have he1 : Real.exp 1 ≤ (11 / 4 : ℝ) := by
          linarith only [Real.exp_one_lt_d9]
        have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he1 45
        have hp' : Real.exp 45 ≤ (11 / 4 : ℝ)^45 := by
          have heq : Real.exp (1 : ℝ) ^ (45 : ℕ) = Real.exp 45 := by
            rw [← Real.exp_nat_mul]
            norm_num
          rwa [heq] at hp
        exact hp'.trans (by norm_num)
      have hfactor : (0 : ℝ) ≤ 1 - 1 / 28000000 := by norm_num
      have hy45 : Real.exp 45 ≤ x * (1 - 1 / 28000000) :=
        he45.trans (mul_le_mul_of_nonneg_right hx20 hfactor)
      have hyx : x * (1 - 1 / 28000000) ≤ x := by nlinarith only [hx0]
      obtain ⟨p, hp, hlow, hupp⟩ := prime_interval_of_middle_estimate x hx20
        (hmid _ hy45 (hyx.trans h301)) (hmid x (hy45.trans hyx) h301)
      refine ⟨p, hp, hupp, ?_⟩
      norm_num
      linarith only [hlow]

end ShortPrimeIntervals


theorem solution (x : ℝ) (hx : Real.exp 301 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ x - p ≤ x / (2.8 * 10^7) := by
  obtain ⟨p, hp, hlow, hupp⟩ := ShortPrimeIntervals.prime_interval_above_exp301 x hx
  refine ⟨p, hp, hupp, ?_⟩
  norm_num
  linarith only [hlow]
