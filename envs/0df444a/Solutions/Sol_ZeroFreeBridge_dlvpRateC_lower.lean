-- Prove2me | solution 1 for ZeroFreeBridge.dlvpRateC_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:33:21.118608+00:00
-- url     : https://prove2.me/submissions/acc9d9ee-57ad-4a76-bc5e-52a0cd545235

import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Mathlib

/- PHASE 4 (dVP frontier, the EFFECTIVE rate): `dlvp_zeta_region_rate` with an EXPLICIT constant.

   `dlvp_zeta_region_rate` concludes `∃ c > 0, β ≤ 1 - c/log|γ|` with `c` non-effective (its `A`
   came from Mathlib's bare-`∃` pole constant).  Here we use `hpole_effective` (explicit `A₀ = 16`,
   `ε₀ = 1/48`) instead, so `A = 16` is fixed and `c = dlvpRateC` is a CONCRETE closed-form real
   (built only from `π`, `log(23/22)`, `log(15/(2-π²/6))` — all effective).  With `A = 16` the width
   `σ - 1 = 1/(2(48 + 80L)) ≤ 1/96 < 1/48`, so `hpole_effective` applies with no neighborhood
   threshold on `L`.

   conjecture1_proved = False (NOT a proof of RH; a kernel-verified reduction for a concrete zero).
-/






open Complex MeromorphicOn Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge










theorem solution : (9 / 1369088 : ℝ) ≤ dlvpRateC := by
  have hpilt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpigt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpisq_lt : Real.pi ^ 2 < 9.87 := by nlinarith [hpilt, hpigt, hpi_pos]
  have hden_pos : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by nlinarith [hpisq_lt]
  have hlog2322 : (1 / 25 : ℝ) ≤ Real.log ((23 / 16) / (11 / 8)) := by
    have h2322 : ((23 / 16) / (11 / 8) : ℝ) = 23 / 22 := by norm_num
    rw [h2322, Real.le_log_iff_exp_le (by norm_num)]
    have hb := Real.exp_bound' (x := (1/25 : ℝ)) (by norm_num) (by norm_num) (n := 3) (by norm_num)
    have hsum : (∑ m ∈ Finset.range 3, (1/25 : ℝ) ^ m / m.factorial)
        + (1/25 : ℝ) ^ 3 * (3 + 1) / ((Nat.factorial 3) * 3) ≤ 23 / 22 := by
      simp [Finset.sum_range_succ, Nat.factorial]; norm_num
    linarith [hb, hsum]
  have hlog15 : Real.log (15 / (2 - Real.pi ^ 2 / 6)) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h43 : (15 : ℝ) / (2 - Real.pi ^ 2 / 6) ≤ 43 := by
      rw [div_le_iff₀ hden_pos]; nlinarith [hpisq_lt]
    have hexp4 : (43 : ℝ) ≤ Real.exp 4 := by
      have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have hpow : (2.7 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he1 4
      rw [h4]; nlinarith [hpow]
    linarith [h43, hexp4]
  have hLrpos : 0 < Real.log ((23 / 16) / (11 / 8)) := by linarith [hlog2322]
  have hlog15nn : 0 ≤ Real.log (15 / (2 - Real.pi ^ 2 / 6)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hden_pos]; nlinarith [hden_pos])
  set L1 : ℝ := Real.log ((23 / 16) / (11 / 8)) with hL1
  set L15 : ℝ := Real.log (15 / (2 - Real.pi ^ 2 / 6)) with hL15
  set M : ℝ := (8 / (3 * L1) + 608 / 9) / 16 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hterm : 8 / (3 * L1) ≤ 200 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hlog2322, hLrpos]
  have hMup : M ≤ 151 / 18 := by
    have h1 : M ≤ (200 / 3 + 608 / 9) / 16 := by rw [hMdef]; gcongr
    nlinarith [h1]
  set K : ℝ := 1 + 2 * M * (L15 + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hKub : K ≤ 764 / 9 := by
    rw [hKdef]
    have hfac : L15 + 1 ≤ 4 + 1 := by linarith [hlog15]
    have hfac_pos : 0 < L15 + 1 := by linarith [hlog15nn]
    nlinarith [hMpos, hMup, hfac, hfac_pos, hlog15nn]
  have hCdef : dlvpRateC = 1 / (112 * 16 * K) := by
    rw [dlvpRateC, dlvpRateK, ← hL1, ← hL15, ← hMdef, ← hKdef]
  rw [hCdef]
  have hval : (9 / 1369088 : ℝ) = 1 / (112 * 16 * (764 / 9)) := by norm_num
  rw [hval]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [hKub, hKpos]
