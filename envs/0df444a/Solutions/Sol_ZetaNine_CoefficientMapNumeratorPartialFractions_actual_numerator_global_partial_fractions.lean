-- Prove2me | solution 1 for ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-07T08:18:03.07975+00:00
-- url     : https://prove2.me/submissions/0f06a3fa-77af-4e92-9f12-9f6547bcd311

import Definitions.Def_ZetaNine_CoefficientMapNumeratorPF
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 3000000





set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset
open Polynomial

namespace ZetaNine.CoefficientMap























theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  intro hz
  have he : (k : ℚ) = (j : ℚ) := by linarith
  exact hkj (Nat.cast_inj.mp he)































end ZetaNine.CoefficientMap














set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity























theorem pole_factors_coprime (a b : ℕ) (hab : a ≠ b) :
    IsCoprime ((X + C (a : ℚ)) ^ 9) ((X + C (b : ℚ)) ^ 9) := by
  have hneq : (-(a : ℚ)) ≠ -(b : ℚ) := by
    intro h
    exact hab (Nat.cast_inj.mp (neg_inj.mp h))
  have hc := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero_of_ne hneq).isUnit
  have hp := hc.pow (m := 9) (n := 9)
  simpa only [map_neg, sub_neg_eq_add] using hp



theorem polePolynomial_natDegree (n : ℕ) : (polePolynomial n).natDegree = n + 1 := by
  unfold polePolynomial
  rw [Polynomial.natDegree_prod_of_monic (range (n + 1))
    (fun j : ℕ => X + C (j : ℚ)) (fun j hj => Polynomial.monic_X_add_C (j : ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  simp

theorem polePolynomial_pow_natDegree (n : ℕ) : (polePolynomial n ^ 9).natDegree = 9 * (n + 1) := by
  rw [Polynomial.natDegree_pow, polePolynomial_natDegree]





















end ZetaNine.CoefficientMapInjectivity















set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet




















theorem shiftedVariable_eval (j : ℕ) (z : ℚ) :
    (shiftedVariable j).eval z = -(j : ℚ) + z := by
  simp [shiftedVariable]
  ring



theorem shiftedClearedDenominator_eval (n j : ℕ) (z : ℚ) :
    (shiftedClearedDenominator n j).eval z = ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ) + z) := by
  simp only [shiftedClearedDenominator, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_C, shiftedVariable_eval]
  rfl











theorem shiftedClearedDenominator_constant (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) =
      ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shiftedClearedDenominator_eval]
  simp

theorem shiftedClearedDenominator_constant_ne_zero (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) ≠ 0 := by
  rw [shiftedClearedDenominator_constant]
  exact ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero n j



















end ZetaNine.CoefficientMapJet
















set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

open CoefficientMapInjectivity







-- The actual coefficients, not arbitrary coefficient parameters.




theorem clearedPolePolynomial_comp_shift (n j : ℕ) :
    (clearedPolePolynomial n j).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator n j := by
  simp only [clearedPolePolynomial, CoefficientMapJet.shiftedClearedDenominator,
    Polynomial.prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]







theorem truncation_remainder_X_pow_dvd (S : PowerSeries ℚ) :
    (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ S - (PowerSeries.trunc 9 S : PowerSeries ℚ) := by
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro k hk
  simp only [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hk, sub_self]

theorem polynomial_X_pow_dvd_of_series (P : ℚ[X])
    (h : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣ (P : PowerSeries ℚ)) :
    (X : ℚ[X]) ^ 9 ∣ P := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  simpa only [Polynomial.coeff_coe] using PowerSeries.X_pow_dvd_iff.mp h k hk









theorem shifted_divisibility_implies_pole_divisibility (P : ℚ[X]) (j : ℕ)
    (h : (X : ℚ[X]) ^ 9 ∣ P.comp (CoefficientMapJet.shiftedVariable j)) :
    (X + C (j : ℚ)) ^ 9 ∣ P := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
  simpa only [Polynomial.comp_assoc, CoefficientMapJet.shiftedVariable,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
    Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he







-- This uses the local truncation/divisibility result, without global PF or properness.




theorem clearedPolePolynomial_natDegree (n j : ℕ) (hj : j ≤ n) :
    (clearedPolePolynomial n j).natDegree = n := by
  unfold clearedPolePolynomial
  rw [Polynomial.natDegree_prod_of_monic ((range (n + 1)).erase j)
    (fun k : ℕ => X + C (k : ℚ)) (fun k hk => Polynomial.monic_X_add_C (k : ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  simp [Nat.lt_succ_of_le hj]









theorem polePolynomial_eval (n : ℕ) (t : ℚ) :
    (polePolynomial n).eval t = CoefficientMap.poleProduct n t := by
  simp only [polePolynomial, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rfl

theorem polePolynomial_eval_ne_zero (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : (polePolynomial n).eval t ≠ 0 := by
  rw [polePolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact hregular k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem polePolynomial_eval_factor (n j : ℕ) (t : ℚ) (hj : j ≤ n) :
    (polePolynomial n).eval t = (t + (j : ℚ)) * (clearedPolePolynomial n j).eval t := by
  simp only [polePolynomial, clearedPolePolynomial, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact (Finset.mul_prod_erase (range (n + 1)) (fun k => t + (k : ℚ))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).symm







end ZetaNine.CoefficientMapPartialFractions


















set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapNumeratorPartialFractions

open CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData









theorem numeratorClearedSeries_denominator_identity (m j : ℕ) (A : ℚ[X]) :
    numeratorClearedSeries m j A *
      (CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
        (A.comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff
      ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero m j)
  unfold numeratorClearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]



theorem numeratorLocalTruncation_comp_eq_sum (m j : ℕ) (A : ℚ[X]) :
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ)) =
      ∑ s ∈ Icc 1 9, C (numeratorLocalCoefficient m j s A) *
        (X + C (j : ℚ)) ^ (9 - s) := by
  unfold numeratorLocalTruncation Polynomial.comp
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_nbij' (fun k : ℕ => 9 - k) (fun s : ℕ => 9 - s)
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [Finset.mem_Icc]
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    rw [Finset.mem_range]
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    have he : 9 - (9 - k) = k := by omega
    simp only [numeratorLocalCoefficient, he]

theorem numeratorPartialNumerator_eq_sum_blocks (m : ℕ) (A : ℚ[X]) :
    numeratorPartialNumerator m A = ∑ j ∈ range (m + 1), numeratorPartialBlock m j A := by
  unfold numeratorPartialNumerator numeratorPartialBlock
  apply Finset.sum_congr rfl
  intro j hj
  rw [numeratorLocalTruncation_comp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem numeratorPartialBlock_comp_own_shift (m j : ℕ) (A : ℚ[X]) :
    (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator m j ^ 9 * numeratorLocalTruncation m j A := by
  rw [numeratorPartialBlock, Polynomial.mul_comp, Polynomial.pow_comp,
    clearedPolePolynomial_comp_shift]
  simp only [Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel, Polynomial.comp_X]

theorem numerator_own_block_matches_nine_jets (m j : ℕ) (A : ℚ[X]) :
    (X : ℚ[X]) ^ 9 ∣ A.comp (CoefficientMapJet.shiftedVariable j) -
      (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) := by
  apply polynomial_X_pow_dvd_of_series
  have h := dvd_mul_of_dvd_left
    (truncation_remainder_X_pow_dvd (numeratorClearedSeries m j A))
    ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)
  rw [numeratorPartialBlock_comp_own_shift]
  convert h using 1
  rw [sub_mul, numeratorClearedSeries_denominator_identity]
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
    numeratorLocalTruncation]
  ring

theorem numerator_different_block_pole_divisibility (m i j : ℕ) (A : ℚ[X])
    (hj : j ≤ m) (hji : j ≠ i) :
    (X + C (j : ℚ)) ^ 9 ∣ numeratorPartialBlock m i A := by
  have hjmem : j ∈ (range (m + 1)).erase i := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨hji, Nat.lt_succ_of_le hj⟩
  have hbase : X + C (j : ℚ) ∣ clearedPolePolynomial m i :=
    Finset.dvd_prod_of_mem (fun k : ℕ => X + C (k : ℚ)) hjmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hbase 9) _

theorem numerator_different_block_shift_X_pow_dvd (m i j : ℕ) (A : ℚ[X])
    (hj : j ≤ m) (hji : j ≠ i) :
    (X : ℚ[X]) ^ 9 ∣ (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
  obtain ⟨q, hq⟩ := numerator_different_block_pole_divisibility m i j A hj hji
  refine ⟨q.comp (CoefficientMapJet.shiftedVariable j), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (CoefficientMapJet.shiftedVariable j)) hq
  simpa only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel] using he

theorem numerator_full_candidate_matches_nine_jets (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    (X : ℚ[X]) ^ 9 ∣
      (A - numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) := by
  have hjmem : j ∈ range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsplit : (numeratorPartialNumerator m A).comp (CoefficientMapJet.shiftedVariable j) =
      (numeratorPartialBlock m j A).comp (CoefficientMapJet.shiftedVariable j) +
        ∑ i ∈ (range (m + 1)).erase j,
          (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
    rw [numeratorPartialNumerator_eq_sum_blocks, Polynomial.sum_comp]
    exact (Finset.add_sum_erase (range (m + 1))
      (fun i => (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j)) hjmem).symm
  have hoff : (X : ℚ[X]) ^ 9 ∣ ∑ i ∈ (range (m + 1)).erase j,
      (numeratorPartialBlock m i A).comp (CoefficientMapJet.shiftedVariable j) := by
    apply Finset.dvd_sum
    intro i hi
    exact numerator_different_block_shift_X_pow_dvd m i j A hj (Finset.ne_of_mem_erase hi).symm
  rw [Polynomial.sub_comp, hsplit, sub_add_eq_sub_sub]
  exact dvd_sub (numerator_own_block_matches_nine_jets m j A) hoff

theorem numerator_denominator_divides_actual_candidate_difference (m : ℕ) (A : ℚ[X]) :
    polePolynomial m ^ 9 ∣ A - numeratorPartialNumerator m A := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    apply shifted_divisibility_implies_pole_divisibility
    exact numerator_full_candidate_matches_nine_jets m j A
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))







theorem numeratorLocalTruncation_natDegree_le (m j : ℕ) (A : ℚ[X]) :
    (numeratorLocalTruncation m j A).natDegree ≤ 8 := by
  have h := PowerSeries.natDegree_trunc_lt (numeratorClearedSeries m j A) 8
  exact Nat.le_of_lt_succ h

theorem numeratorPartialBlock_natDegree_le (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    (numeratorPartialBlock m j A).natDegree ≤ 9 * m + 8 := by
  have hm := Polynomial.natDegree_mul_le (p := clearedPolePolynomial m j ^ 9)
    (q := (numeratorLocalTruncation m j A).comp (X + C (j : ℚ)))
  have hc := Polynomial.natDegree_comp_le
    (p := numeratorLocalTruncation m j A) (q := X + C (j : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hc
  rw [Polynomial.natDegree_pow, clearedPolePolynomial_natDegree m j hj] at hm
  have ht := numeratorLocalTruncation_natDegree_le m j A
  unfold numeratorPartialBlock
  omega

theorem numeratorPartialNumerator_natDegree_le (m : ℕ) (A : ℚ[X]) :
    (numeratorPartialNumerator m A).natDegree ≤ 9 * m + 8 := by
  rw [numeratorPartialNumerator_eq_sum_blocks]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact numeratorPartialBlock_natDegree_le m j A
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem actual_numerator_polynomial_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) : A = numeratorPartialNumerator m A := by
  have hdvd := numerator_denominator_divides_actual_candidate_difference m A
  have hzero : A - numeratorPartialNumerator m A = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [polePolynomial_pow_natDegree] at hdeg
    have hp := numeratorPartialNumerator_natDegree_le m A
    have hdiff := Polynomial.natDegree_sub_le A (numeratorPartialNumerator m A)
    rcases le_total A.natDegree (numeratorPartialNumerator m A).natDegree with h | h
    · rw [max_eq_right h] at hdiff
      omega
    · rw [max_eq_left h] at hdiff
      omega
  exact sub_eq_zero.mp hzero

theorem numerator_partial_term_division (m j s : ℕ) (A : ℚ[X]) (t : ℚ) (hj : j ≤ m)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    (numeratorLocalCoefficient m j s A * (clearedPolePolynomial m j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial m).eval t ^ 9 =
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff (pow_ne_zero _ (polePolynomial_eval_ne_zero m t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [polePolynomial_eval_factor m j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = numeratorLocalCoefficient m j s A * (clearedPolePolynomial m j).eval t ^ 9 *
        ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem checked_actual_numerator_global_partial_fractions (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s := by
  conv_lhs => rw [actual_numerator_polynomial_partial_fractions m A hproper]
  simp only [numeratorPartialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact numerator_partial_term_division m j s A t
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular



theorem numeratorLocalCoefficient_sub (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A - B) =
      numeratorLocalCoefficient m j s A - numeratorLocalCoefficient m j s B := by
  simp only [numeratorLocalCoefficient, numeratorClearedSeries,
    Polynomial.sub_comp, Polynomial.coe_sub, sub_mul, map_sub]

theorem actual_numerator_all_local_coefficients_zero_implies_zero (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1))
    (hzero : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 → numeratorLocalCoefficient m j s A = 0) :
    A = 0 := by
  have hp : numeratorPartialNumerator m A = 0 := by
    unfold numeratorPartialNumerator
    apply Finset.sum_eq_zero
    intro j hj
    apply Finset.sum_eq_zero
    intro s hs
    rw [hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) s
      (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
    simp
  exact (actual_numerator_polynomial_partial_fractions m A hproper).trans hp

theorem actual_numerator_local_coefficients_injective (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (heq : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B := by
  have hdiff : (A - B).natDegree < 9 * (m + 1) := by
    have hdeg := Polynomial.natDegree_sub_le A B
    rcases le_total A.natDegree B.natDegree with h | h
    · rw [max_eq_right h] at hdeg
      omega
    · rw [max_eq_left h] at hdeg
      omega
  have hzero : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s (A - B) = 0 := by
    intro j hj s hs1 hs9
    rw [numeratorLocalCoefficient_sub, heq j hj s hs1 hs9, sub_self]
  exact sub_eq_zero.mp (actual_numerator_all_local_coefficients_zero_implies_zero m (A - B) hdiff hzero)

end ZetaNine.CoefficientMapNumeratorPartialFractions












open scoped BigOperators
open Finset Polynomial ZetaNine ZetaNine.CoefficientMapNumeratorPartialFractions ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem solution (m : ℕ) (A : ℚ[X])
    (hproper : A.natDegree < 9 * (m + 1)) (t : ℚ)
    (hregular : ∀ k ≤ m, t + (k : ℚ) ≠ 0) :
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s := by
  exact ZetaNine.CoefficientMapNumeratorPartialFractions.checked_actual_numerator_global_partial_fractions m A hproper t hregular

#print axioms solution
