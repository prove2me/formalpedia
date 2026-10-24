-- Prove2me | solution 1 for UniversalBarrier.NSC.ineq_9
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:50:29.470817+00:00
-- url     : https://prove2.me/submissions/a7a6f038-040b-4411-b2cd-740e00a9f0d6

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC.EllProof

lemma cubic_bound (a t : ℝ) (ha : 1 ≤ a) (ht : 0 ≤ t) :
    a*t^3+3*a*t+a^2-1 ≤ a*Real.sqrt (a^2+1)*Real.sqrt (1+t^2)^3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb : Real.sqrt (a^2+1)^2 = a^2+1 := Real.sq_sqrt (by positivity)
  have hd : Real.sqrt (1+t^2)^2 = 1+t^2 := Real.sq_sqrt (by positivity)
  have hrest : 0 ≤ a^2*t^4+3*a^2*t^2+2*a*t^3+4*a*t := by positivity
  have hpoly : 0 ≤ a^2*t^4+3*a^2*t^2+3*a^2+2*a*t^3+4*a*t-1 := by
    nlinarith [sq_nonneg (a-1)]
  have hid : (a*Real.sqrt (a^2+1)*Real.sqrt (1+t^2)^3)^2 -
      (a*t^3+3*a*t+a^2-1)^2 =
      (a*t-1)^2 * (a^2*t^4+3*a^2*t^2+3*a^2+2*a*t^3+4*a*t-1) := by
    calc
      _ = a^2 * Real.sqrt (a^2+1)^2 * (Real.sqrt (1+t^2)^2)^3 -
          (a*t^3+3*a*t+a^2-1)^2 := by ring
      _ = a^2*(a^2+1)*(1+t^2)^3 - (a*t^3+3*a*t+a^2-1)^2 := by rw [hb,hd]
      _ = _ := by ring
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith only [hid, mul_nonneg (sq_nonneg (a*t-1)) hpoly]

lemma rpow_three_halves (t : ℝ) :
    (1+t^2)^((3:ℝ)/2) = Real.sqrt (1+t^2)^3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  norm_num

lemma ell_bound_nonneg (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    ell n t ≤ 2*Real.sqrt ((n:ℝ)+1) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 1 ≤ Real.sqrt n := by simpa using Real.sqrt_le_sqrt hnR
  have ha0 : 0 < Real.sqrt n := by linarith
  have ha2 : Real.sqrt n ^ 2 = (n:ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hraw := cubic_bound (Real.sqrt n) t ha ht
  rw [ha2] at hraw
  have hnum : 2*t^3+6*t+4*cn n ≤
      2*Real.sqrt ((n:ℝ)+1)*Real.sqrt (1+t^2)^3 := by
    apply (mul_le_mul_iff_left₀ ha0).mp
    calc
      (2*t^3+6*t+4*cn n)*Real.sqrt n =
          2*(Real.sqrt n*t^3+3*Real.sqrt n*t+(n:ℝ)-1) := by
        unfold cn
        field_simp
        ring
      _ ≤ 2*(Real.sqrt n*Real.sqrt ((n:ℝ)+1)*Real.sqrt (1+t^2)^3) :=
        mul_le_mul_of_nonneg_left hraw (by norm_num)
      _ = (2*Real.sqrt ((n:ℝ)+1)*Real.sqrt (1+t^2)^3)*Real.sqrt n := by ring
  rw [ell, rpow_three_halves]
  exact (div_le_iff₀ (by positivity)).mpr hnum

end UniversalBarrier.NSC.EllProof

namespace UniversalBarrier.NSC

open EllProof

theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ell n t ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
  have ht3 : t^3 ≤ |t|^3 := (le_abs_self (t^(3:ℕ))).trans_eq (abs_pow t 3)
  have hnum : 2*t^3+6*t+4*cn n ≤ 2*|t|^3+6*|t|+4*cn n := by
    linarith [le_abs_self t]
  calc
    ell n t ≤ ell n |t| := by
      unfold ell
      rw [sq_abs]
      exact div_le_div_of_nonneg_right hnum (Real.rpow_nonneg (by positivity) _)
    _ ≤ _ := ell_bound_nonneg n hn |t| (abs_nonneg t)

end UniversalBarrier.NSC
