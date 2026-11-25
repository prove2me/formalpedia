-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__mass_pow_le_exp_rpow_18515efb5c9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:54:27.881216+00:00
-- url     : https://prove2.me/submissions/9aacf9f6-816f-48cf-93ba-65c0e0d6627f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_MassPowLeExpRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.BridgeLemma₂
private theorem const_20736_le_exp_15 : (20736 : ℝ) ≤ Real.exp 15 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (20736 : ℝ) ≤ 2 ^ 15 := by norm_num
    _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) h1 15
end Formalism.MainNotions.BridgeLemma₂
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (f m : ℕ) (rd L B₁ C κ : ℝ) (hf : 1 ≤ f) (hm : 2 ≤ m) (hrd : 2 ≤ rd) (hL : 1 ≤ L) (hκ : 1 ≤ κ)
    (hlf : Real.log f ≤ m) (hlrd : Real.log rd ≤ κ * L) (hB0 : 0 ≤ B₁) (hB : B₁ ≤ 4 * f * rd) (hC : 55 * κ ≤ C ^ 2) :
    (1 + 2 * B₁) ^ (2 * (2 * f)) * (1 + 2 * (B₁ * rd)) ^ (2 * (2 * f)) * (B₁ * (B₁ * rd)) ^ (4 * (2 * f)) ≤
      (Real.exp L ^ (C * (m : ℝ) ^ 2 * f)) ^ C := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hfpos : (0 : ℝ) < f := by linarith
  have hrdpos : (0 : ℝ) < rd := by linarith
  have hfe : (f : ℝ) ≤ Real.exp m := (Real.log_le_iff_le_exp hfpos).1 hlf
  have hre : rd ≤ Real.exp (κ * L) := (Real.log_le_iff_le_exp hrdpos).1 hlrd
  have hfr : (1 : ℝ) ≤ f * rd := by nlinarith
  have hfr2 : (1 : ℝ) ≤ f * rd ^ 2 := by nlinarith
  have hBr0 : 0 ≤ B₁ * rd := mul_nonneg hB0 hrdpos.le
  have hBr : B₁ * rd ≤ 4 * f * rd * rd := mul_le_mul_of_nonneg_right hB hrdpos.le
  have ha : 1 + 2 * B₁ ≤ 9 * f * rd := by nlinarith
  have hb : 1 + 2 * (B₁ * rd) ≤ 9 * f * rd ^ 2 := by nlinarith
  have hc : B₁ * (B₁ * rd) ≤ 16 * (f : ℝ) ^ 2 * rd ^ 3 := by
    have h := mul_le_mul hB hBr hBr0 (by linarith)
    calc B₁ * (B₁ * rd) ≤ 4 * f * rd * (4 * f * rd * rd) := h
      _ = 16 * (f : ℝ) ^ 2 * rd ^ 3 := by ring
  have hQ0 : 0 ≤ (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hQ : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
      Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) := by
    have hc2 : (B₁ * (B₁ * rd)) ^ 2 ≤ (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hB0 hBr0) hc 2
    have hab : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) ≤ (9 * f * rd) * (9 * f * rd ^ 2) :=
      mul_le_mul ha hb (by linarith) (by linarith)
    have h1 : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
        (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      mul_le_mul hab hc2 (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    have h2 : (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 =
        20736 * (f : ℝ) ^ 6 * rd ^ 9 := by ring
    have hf6 : (f : ℝ) ^ 6 ≤ Real.exp m ^ 6 := pow_le_pow_left₀ hfpos.le hfe 6
    have hr9 : rd ^ 9 ≤ Real.exp (κ * L) ^ 9 := pow_le_pow_left₀ hrdpos.le hre 9
    have h3 : 20736 * (f : ℝ) ^ 6 * rd ^ 9 ≤ Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 :=
      mul_le_mul (mul_le_mul const_20736_le_exp_15 hf6 (by positivity) (by positivity)) hr9
        (pow_nonneg hrdpos.le 9) (by positivity)
    have h4 : Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 := by
      rw [Real.exp_add, Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    rw [h4]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  have key : 60 + 24 * (m : ℝ) + 36 * (κ * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) := by
    have y1 : 1 ≤ κ * L := by nlinarith
    have hmm : 2 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hyl : (m : ℝ) ^ 2 ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hy4 : 4 * (κ * L) ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hCk : 55 * κ * ((m : ℝ) ^ 2 * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
    nlinarith
  have hexp : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) ≤
      L * (C * (m : ℝ) ^ 2 * f) * C := by
    have e1 : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        (f : ℝ) * (60 + 24 * (m : ℝ) + 36 * (κ * L)) := by push_cast; ring
    have e2 : L * (C * (m : ℝ) ^ 2 * f) * C = (f : ℝ) * (C ^ 2 * ((m : ℝ) ^ 2 * L)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hfpos.le
  have hpow : 4 * (2 * f) = 2 * (2 * (2 * f)) := by ring
  rw [hpow, pow_mul (B₁ * (B₁ * rd)) 2 (2 * (2 * f)), ← mul_pow, ← mul_pow, ← Real.exp_mul,
    ← Real.exp_mul]
  calc _ ≤ (Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L))) ^ (2 * (2 * f)) :=
        pow_le_pow_left₀ hQ0 hQ _
    _ = Real.exp (((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L))) :=
        (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * (C * (m : ℝ) ^ 2 * f) * C) := Real.exp_le_exp.2 hexp
end Formalism.MainNotions.BridgeLemma₂
