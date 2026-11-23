-- Prove2me | solution 1 for SumProduct.dedekindZeta_two_re_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:35.717471+00:00
-- url     : https://prove2.me/submissions/2953e7f8-9015-433e-a0b5-cdaa99be983a

import Mathlib
import Definitions.Def_SumProduct_EulerBound
import Theorems.Thm_SumProduct_idealCountArith_apply_ne
import Theorems.Thm_SumProduct_idealCount_le_zeta_pow
import Theorems.Thm_SumProduct_LSeriesSummable_and_LSeries_zeta_pow
attribute [local simp] SumProduct.idealCountArith_apply_ne

set_option autoImplicit true
open scoped NumberField
open NumberField UniqueFactorizationMonoid
open SumProduct
variable {K : Type*} [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] :
    (NumberField.dedekindZeta K (2 : ℂ)).re ≤ 2 ^ Module.finrank ℚ K := by
  set d := Module.finrank ℚ K with hd
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  obtain ⟨hbsum, hbeq⟩ := LSeriesSummable_and_LSeries_zeta_pow h2 d
  set ra : ℕ → ℝ := fun n => (idealCount K n : ℝ) / (n : ℝ) ^ 2 with hra
  set rb : ℕ → ℝ :=
    fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℝ) / (n : ℝ) ^ 2 with hrb
  -- The L-series term at `s = 2` is the (cast of the) real coefficient.
  have htermA : ∀ n, LSeries.term (fun n => (idealCount K n : ℂ)) 2 n = (ra n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hra]
    · rw [LSeries.term_of_ne_zero hn.ne', hra, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
      push_cast; ring
  have htermB : ∀ n, LSeries.term
      (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2 n
        = (rb n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hrb]
    · rw [LSeries.term_of_ne_zero hn.ne', hrb, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
      push_cast; ring
  -- Real summability of both coefficient series, and the pointwise bound.
  have hrbsum : Summable rb := by
    have h : Summable (LSeries.term
        (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2) := hbsum
    exact (Complex.summable_ofReal).mp (h.congr htermB)
  have hra_le : ∀ n, ra n ≤ rb n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hra, hrb]
    · have hle : (idealCount K n : ℝ)
          ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℝ) := by
        exact_mod_cast idealCount_le_zeta_pow hn.ne'
      simp only [hra, hrb]; gcongr
  have hrasum : Summable ra := Summable.of_nonneg_of_le (fun n => by positivity) hra_le hrbsum
  have hasum : LSeriesSummable (fun n => (idealCount K n : ℂ)) 2 := by
    have h1 : Summable (fun n => ((ra n : ℝ) : ℂ)) := (Complex.summable_ofReal).mpr hrasum
    exact h1.congr (fun n => (htermA n).symm)
  -- `(dedekindZeta K 2).re = ∑ a_n/n²`.
  have hzeta : (NumberField.dedekindZeta K (2 : ℂ)).re = ∑' n, ra n := by
    change (∑' n, LSeries.term (fun n => (idealCount K n : ℂ)) 2 n).re = ∑' n, ra n
    rw [Complex.re_tsum hasum]
    exact tsum_congr fun n => by rw [htermA n, Complex.ofReal_re]
  -- `∑ d_d(n)/n² = (π²/6)^d`.
  have hbre : (∑' n, rb n) = (Real.pi ^ 2 / 6) ^ d := by
    have h : (((∑' n, rb n : ℝ)) : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ^ d := by
      rw [Complex.ofReal_tsum]
      calc ∑' n, ((rb n : ℝ) : ℂ)
          = LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2 :=
            tsum_congr fun n => (htermB n).symm
        _ = riemannZeta 2 ^ d := hbeq
        _ = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ^ d := by rw [riemannZeta_two]; push_cast; ring
    exact_mod_cast h
  rw [hzeta]
  calc ∑' n, ra n
      ≤ ∑' n, rb n := Summable.tsum_le_tsum hra_le hrasum hrbsum
    _ = (Real.pi ^ 2 / 6) ^ d := hbre
    _ ≤ 2 ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [Real.pi_lt_d2, Real.pi_pos]
end SumProduct
