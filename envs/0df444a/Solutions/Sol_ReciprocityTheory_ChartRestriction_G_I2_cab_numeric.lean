-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_numeric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:08.819867+00:00
-- url     : https://prove2.me/submissions/38610e1d-88ee-4658-b534-e2fea08f195d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (c G gA g' dst : ℕ) (q t0 : ℝ) (hq : 2 ≤ q) (hG : G ≤ gA) (hg' : 2 * g' ≤ dst)
    (hC5 : 4 * c * (7 + Real.log (q * c)) + dst + 1 ≤ t0) (hC6 : gA * Real.log 2 ≤ t0) :
    Real.sqrt (12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c) *
        (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
        (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial := by
  have hq0 : 0 < q := by linarith
  have hqc : 0 < q * (c + 1) := by positivity
  have hf1 : (1 : ℝ) ≤ c.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero c)
  set Y := (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
    (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) with hY
  have hY0 : 0 ≤ Y := by positivity
  set Bsq := 12 * (5.12 : ℝ) ^ G * c.factorial * (2 / (q * Real.pi)) ^ c with hBsq
  have hB0 : 0 ≤ Bsq := by positivity
  set RHS := 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * c.factorial with hRHS
  have hR0 : 0 ≤ RHS := by positivity
  have hr : ((q * (c + 1)) ^ ((c : ℝ) / 2)) ^ 2 = (q * (c + 1)) ^ c := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hqc.le, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have e1 : Real.exp (-(Real.pi * t0)) = Real.exp (-((Real.pi - 2) * t0)) * Real.exp (-2 * t0) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : (2 * (c + 1) / Real.pi) ^ c = (2 / (q * Real.pi)) ^ c * (q * (c + 1)) ^ c := by
    rw [← mul_pow]; congr 1; field_simp
  have hY2 : Y ^ 2 = (q * (c + 1)) ^ c * Real.exp (5 * Real.pi * c) * (4 * 81 ^ g' * Real.exp (-(Real.pi * t0))) := by
    rw [hY, mul_pow, mul_pow, hr, mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      show (81 : ℝ) ^ g' = (9 ^ g') ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring_nf
  have hBY : Bsq * Y ^ 2 = 48 * c.factorial * 81 ^ g' * Real.exp (-2 * t0) *
      ((5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0))) := by
    rw [hY2, e1, e2, hBsq]; ring
  have hK := cab_key c gA q t0 hq dst (Nat.cast_nonneg dst) hC5 hC6
  have h81 : (81 : ℝ) ^ g' ≤ 18.49 ^ dst := by
    calc (81 : ℝ) ^ g' = 9 ^ (2 * g') := by rw [pow_mul]; norm_num
      _ ≤ 9 ^ dst := pow_le_pow_right₀ (by norm_num) hg'
      _ ≤ 18.49 ^ dst := pow_le_pow_left₀ (by norm_num) (by norm_num) dst
  have hG' : (5.12 : ℝ) ^ G ≤ 5.12 ^ gA := pow_le_pow_right₀ (by norm_num) hG
  have hsq : Bsq * Y ^ 2 ≤ RHS ^ 2 := by
    rw [hBY]
    have hRHS2 : RHS ^ 2 = 49 * c.factorial * c.factorial * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by
      rw [hRHS, show (18.49 : ℝ) ^ dst = ((4.3 : ℝ) ^ dst) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        show Real.exp (-2 * t0) = Real.exp (-t0) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
        show (4 : ℝ) ^ gA = ((2 : ℝ) ^ gA) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      ring
    rw [hRHS2]
    have hX : (5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
        Real.exp (-((Real.pi - 2) * t0)) ≤ 4 ^ gA := by
      refine le_trans ?_ hK
      gcongr
    have hE : 0 ≤ Real.exp (-2 * t0) := (Real.exp_pos _).le
    calc 48 * (c.factorial : ℝ) * 81 ^ g' * Real.exp (-2 * t0) *
          ((5.12 : ℝ) ^ G * (2 * (c + 1) / Real.pi) ^ c * Real.exp (5 * Real.pi * c) *
            Real.exp (-((Real.pi - 2) * t0)))
        ≤ 48 * (c.factorial : ℝ) * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by gcongr
      _ ≤ 49 * c.factorial * c.factorial * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by
        have : 0 ≤ (18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA := by positivity
        have h2 : 48 * (c.factorial : ℝ) ≤ 49 * c.factorial * c.factorial := by nlinarith
        calc 48 * (c.factorial : ℝ) * 18.49 ^ dst * Real.exp (-2 * t0) * 4 ^ gA
            = (48 * (c.factorial : ℝ)) * ((18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA) := by ring
          _ ≤ (49 * c.factorial * c.factorial) * ((18.49 : ℝ) ^ dst * Real.exp (-2 * t0) * 4 ^ gA) :=
            mul_le_mul_of_nonneg_right h2 this
          _ = _ := by ring
  have hL : Real.sqrt Bsq * (q * (c + 1)) ^ ((c : ℝ) / 2) * Real.exp (5 * Real.pi * c / 2) *
      (2 * 9 ^ g' * Real.exp (-(Real.pi / 2 * t0))) = Real.sqrt Bsq * Y := by
    rw [hY]; ring
  rw [hL]
  calc Real.sqrt Bsq * Y = Real.sqrt (Bsq * Y ^ 2) := by
        rw [Real.sqrt_mul hB0, Real.sqrt_sq hY0]
    _ ≤ Real.sqrt (RHS ^ 2) := Real.sqrt_le_sqrt hsq
    _ = RHS := Real.sqrt_sq hR0
end ReciprocityTheory.ChartRestriction.G.I2
