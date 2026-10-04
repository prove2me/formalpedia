-- Prove2me | solution 1 for ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:29:38.342354+00:00
-- url     : https://prove2.me/submissions/014c288e-ac7b-49fb-bfbe-0a3c7bbfefb5

import Definitions.Def_ZetaNine_CoefficientMapShiftDegree
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic




/-! The actual polynomial shift operator used by the original quartic kernel route.
This file proves its coefficient obstruction; its relation to the genuine rational
telescoper is established separately. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapShiftDegree







theorem actual_nextCoeff_mul (P H : ℚ[X]) :
    (P * H).nextCoeff = P.nextCoeff * H.leadingCoeff + P.leadingCoeff * H.nextCoeff := by
  rw [← coeff_one_reverse, reverse_mul_of_domain, mul_coeff_one]
  simp only [coeff_zero_reverse, coeff_one_reverse]
  ring

theorem actual_shift_nextCoeff (H : ℚ[X]) :
    (H.comp (X + C 1)).nextCoeff = H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff := by
  change (taylor 1 H).nextCoeff = _
  by_cases hd : H.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd]
    simp
  have hdpos : 0 < H.natDegree := Nat.pos_of_ne_zero hd
  rw [nextCoeff_of_natDegree_pos (by simpa using hdpos), natDegree_taylor, taylor_coeff]
  have hdeg : (hasseDeriv (H.natDegree - 1) H).natDegree < 2 := by
    have h := natDegree_hasseDeriv_le H (H.natDegree - 1)
    omega
  rw [eval_eq_sum_range' hdeg 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, one_pow, mul_one,
    hasseDeriv_coeff]
  have hadd : 1 + (H.natDegree - 1) = H.natDegree := by omega
  have hchoose : H.natDegree.choose (H.natDegree - 1) = H.natDegree := by
    have h := Nat.choose_succ_self_right (H.natDegree - 1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ H.natDegree)] using h
  rw [hadd, Nat.choose_self, hchoose, Nat.cast_one, one_mul,
    ← nextCoeff_of_natDegree_pos hdpos, coeff_natDegree]

theorem shiftA_monic (n : ℕ) : (shiftA n).Monic :=
  (monic_X_sub_C _).mul ((monic_X_add_C _).pow 10)

theorem shiftB_monic (n : ℕ) : (shiftB n).Monic :=
  (monic_X.pow 10).mul (monic_X_add_C _)

theorem shiftA_natDegree (n : ℕ) : (shiftA n).natDegree = 11 := by
  rw [shiftA, natDegree_mul (monic_X_sub_C _).ne_zero ((monic_X_add_C _).pow 10).ne_zero]
  simp only [natDegree_X_sub_C, natDegree_pow, natDegree_X_add_C]

theorem shiftB_natDegree (n : ℕ) : (shiftB n).natDegree = 11 := by
  rw [shiftB, natDegree_mul (monic_X.pow 10).ne_zero (monic_X_add_C _).ne_zero]
  simp only [natDegree_pow, natDegree_X, natDegree_X_add_C]

theorem shiftA_nextCoeff (n : ℕ) : (shiftA n).nextCoeff = 9 * (n : ℚ) - 1 := by
  unfold shiftA
  rw [Monic.nextCoeff_mul (monic_X_sub_C _) ((monic_X_add_C _).pow 10),
    Monic.nextCoeff_pow (monic_X_add_C _) 10, nextCoeff_X_sub_C, nextCoeff_X_add_C]
  simp only [nsmul_eq_mul]
  ring

theorem shiftB_nextCoeff (n : ℕ) : (shiftB n).nextCoeff = 2 * (n : ℚ) + 1 := by
  have hX : (X : ℚ[X]).nextCoeff = 0 := by norm_num [nextCoeff]
  unfold shiftB
  rw [Monic.nextCoeff_mul (monic_X.pow 10) (monic_X_add_C _),
    Monic.nextCoeff_pow monic_X 10, hX, nextCoeff_X_add_C]
  simp

theorem actual_shift_difference_coefficient (n : ℕ) (H : ℚ[X]) (hH : H ≠ 0) :
    (shiftDifference n H).coeff (H.natDegree + 10) =
      (7 * (n : ℚ) - 2 - (H.natDegree : ℚ)) * H.leadingCoeff := by
  have hAH : (shiftA n * H).natDegree = 11 + H.natDegree := by
    rw [(shiftA_monic n).natDegree_mul' hH, shiftA_natDegree]
  have hHs : H.comp (X + C 1) ≠ 0 := by
    intro h
    exact hH ((taylor_eq_zero (r := (1 : ℚ)) (f := H)).mp h)
  have hHsdeg : (H.comp (X + C 1)).natDegree = H.natDegree := natDegree_taylor H 1
  have hHslead : (H.comp (X + C 1)).leadingCoeff = H.leadingCoeff := leadingCoeff_taylor 1 H
  have hBH : (shiftB n * H.comp (X + C 1)).natDegree = 11 + H.natDegree := by
    rw [(shiftB_monic n).natDegree_mul' hHs, shiftB_natDegree, hHsdeg]
  have hfirst : (shiftA n * H).coeff (H.natDegree + 10) =
      (9 * (n : ℚ) - 1) * H.leadingCoeff + H.nextCoeff := by
    have hnext := nextCoeff_of_natDegree_pos (p := shiftA n * H) (by omega)
    rw [hAH] at hnext
    rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
    rw [← hnext, actual_nextCoeff_mul, shiftA_nextCoeff, (shiftA_monic n).leadingCoeff,
      one_mul]
  have hsecond : (shiftB n * H.comp (X + C 1)).coeff (H.natDegree + 10) =
      (2 * (n : ℚ) + 1) * H.leadingCoeff +
        (H.nextCoeff + (H.natDegree : ℚ) * H.leadingCoeff) := by
    have hnext := nextCoeff_of_natDegree_pos (p := shiftB n * H.comp (X + C 1)) (by omega)
    rw [hBH] at hnext
    rw [show 11 + H.natDegree - 1 = H.natDegree + 10 by omega] at hnext
    rw [← hnext, actual_nextCoeff_mul, shiftB_nextCoeff, (shiftB_monic n).leadingCoeff,
      one_mul, hHslead, actual_shift_nextCoeff]
  rw [shiftDifference, coeff_sub, hfirst, hsecond]
  ring

theorem actual_shift_difference_coefficient_ne_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    (shiftDifference n H).coeff (H.natDegree + 10) ≠ 0 := by
  rw [actual_shift_difference_coefficient n H hH]
  have hb : H.natDegree + 3 ≤ 7 * n := by omega
  have hbq : (H.natDegree : ℚ) + 3 ≤ 7 * (n : ℚ) := by exact_mod_cast hb
  apply mul_ne_zero
  · have hpos : 0 < 7 * (n : ℚ) - 2 - (H.natDegree : ℚ) := by linarith
    exact ne_of_gt hpos
  · exact leadingCoeff_ne_zero.mpr hH

theorem actual_shift_difference_degree_lower_bound (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hH : H ≠ 0) (hdeg : H.natDegree ≤ 7 * n - 3) :
    H.natDegree + 10 ≤ (shiftDifference n H).natDegree :=
  le_natDegree_of_ne_zero (actual_shift_difference_coefficient_ne_zero n hn H hH hdeg)

theorem checked_actual_shift_difference_small_degree_implies_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 := by
  by_contra hH
  have h := actual_shift_difference_degree_lower_bound n hn H hH hdeg
  omega

end ZetaNine.CoefficientMapShiftDegree








open ZetaNine ZetaNine.CoefficientMapShiftDegree

theorem solution (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 := by
  exact ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_small_degree_implies_zero n hn H hdeg hsmall

#print axioms solution
