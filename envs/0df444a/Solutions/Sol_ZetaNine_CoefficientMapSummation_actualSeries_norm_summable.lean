-- Prove2me | solution 1 for ZetaNine.CoefficientMapSummation.actualSeries_norm_summable
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T21:04:57.840987+00:00
-- url     : https://prove2.me/submissions/cdde6c4d-70cc-4ea6-8208-71b0a16207e7

import Definitions.Def_ZetaNine_CoefficientMapSummation
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMap

open scoped BigOperators
open Finset
open Polynomial

theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  intro hz
  have he : (k : ℚ) = (j : ℚ) := by linarith
  exact hkj (Nat.cast_inj.mp he)

end ZetaNine.CoefficientMap

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet

open scoped BigOperators
open Finset Polynomial

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

theorem clearedSeries_denominator_identity (n j : ℕ) :
    clearedSeries n j * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  unfold clearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem weightedClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
    weightedClearedSeries n j W * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j * W.comp (localU n j) : ℚ[X]) := by
  unfold weightedClearedSeries
  rw [mul_right_comm, clearedSeries_denominator_identity, Polynomial.coe_mul]

end ZetaNine.CoefficientMapJet

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity

open scoped BigOperators
open Finset Polynomial

theorem baseNumerator_eval (n : ℕ) (t : ℚ) :
    (baseNumerator n).eval t = CoefficientMap.numerator n t := by
  simp only [baseNumerator, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rfl

theorem weightedNumerator_shift (n j : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) := by
  simp only [weightedNumerator, baseNumerator, baseU, CoefficientMapJet.shiftedNumerator,
    CoefficientMapJet.localU, Polynomial.mul_comp, Polynomial.prod_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.comp_assoc]

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

theorem baseU_natDegree (n : ℕ) : (baseU n).natDegree = 2 := by
  unfold baseU
  rw [Polynomial.natDegree_mul (Polynomial.X_ne_zero) (Polynomial.X_add_C_ne_zero _)]
  simp only [Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]

theorem baseNumerator_natDegree_le (n : ℕ) : (baseNumerator n).natDegree ≤ 2 * n := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X - C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
      _ = n := by
        simp only [Polynomial.natDegree_X_sub_C]
        simp
  have hR : (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)).natDegree := Polynomial.natDegree_prod_le _ _
      _ = n := by
        simp only [add_assoc, ← map_add, Polynomial.natDegree_X_add_C]
        simp
  have h1 := Polynomial.natDegree_mul_le (p := C ((n.factorial : ℚ) ^ 7))
    (q := ∏ i ∈ range n, (X - C ((i : ℚ) + 1)))
  have h2 := Polynomial.natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 1))))
    (q := ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))
  simp only [Polynomial.natDegree_C, zero_add] at h1
  unfold baseNumerator
  omega

theorem weightedNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).natDegree ≤ 2 * n + 2 * W.natDegree := by
  have hmul := Polynomial.natDegree_mul_le (p := baseNumerator n) (q := W.comp (baseU n))
  have hcomp := Polynomial.natDegree_comp_le (p := W) (q := baseU n)
  rw [baseU_natDegree] at hcomp
  have hbase := baseNumerator_natDegree_le n
  unfold weightedNumerator
  omega

end ZetaNine.CoefficientMapInjectivity

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapPartialFractions

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity

theorem clearedPolePolynomial_comp_shift (n j : ℕ) :
    (clearedPolePolynomial n j).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator n j := by
  simp only [clearedPolePolynomial, CoefficientMapJet.shiftedClearedDenominator,
    Polynomial.prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]

theorem localTruncation_comp_eq_sum (n j : ℕ) (W : ℚ[X]) :
    (localTruncation n j W).comp (X + C (j : ℚ)) =
      ∑ s ∈ Icc 1 9, C (CoefficientMapJet.weightedLocalCoefficient n j s W) *
        (X + C (j : ℚ)) ^ (9 - s) := by
  unfold localTruncation Polynomial.comp
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
    simp only [CoefficientMapJet.weightedLocalCoefficient, he]

theorem partialNumerator_eq_sum_blocks (n : ℕ) (W : ℚ[X]) :
    partialNumerator n W = ∑ j ∈ range (n + 1), partialBlock n j W := by
  unfold partialNumerator partialBlock
  apply Finset.sum_congr rfl
  intro j hj
  rw [localTruncation_comp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem partialBlock_comp_own_shift (n j : ℕ) (W : ℚ[X]) :
    (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) =
      CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * localTruncation n j W := by
  rw [partialBlock, Polynomial.mul_comp, Polynomial.pow_comp, clearedPolePolynomial_comp_shift]
  simp only [Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable,
    sub_add_cancel, Polynomial.comp_X]

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

theorem own_block_matches_nine_jets (n j : ℕ) (W : ℚ[X]) :
    (X : ℚ[X]) ^ 9 ∣
      (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) -
        (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) := by
  apply polynomial_X_pow_dvd_of_series
  have h := dvd_mul_of_dvd_left
    (truncation_remainder_X_pow_dvd (CoefficientMapJet.weightedClearedSeries n j W))
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)
  have he : ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) -
      (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) : ℚ[X]) =
      CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) -
        CoefficientMapJet.shiftedClearedDenominator n j ^ 9 * localTruncation n j W := by
    rw [weightedNumerator_shift, partialBlock_comp_own_shift]
  rw [he]
  convert h using 1
  rw [sub_mul, CoefficientMapJet.weightedClearedSeries_denominator_identity]
  simp only [Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, localTruncation]
  ring

theorem different_block_pole_divisibility (n i j : ℕ) (W : ℚ[X])
    (hj : j ≤ n) (hji : j ≠ i) :
    (X + C (j : ℚ)) ^ 9 ∣ partialBlock n i W := by
  have hjmem : j ∈ (range (n + 1)).erase i := by
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨hji, Nat.lt_succ_of_le hj⟩
  have hbase : X + C (j : ℚ) ∣ clearedPolePolynomial n i :=
    Finset.dvd_prod_of_mem (fun k : ℕ => X + C (k : ℚ)) hjmem
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hbase 9) _

theorem different_block_shift_X_pow_dvd (n i j : ℕ) (W : ℚ[X])
    (hj : j ≤ n) (hji : j ≠ i) :
    (X : ℚ[X]) ^ 9 ∣ (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
  obtain ⟨q, hq⟩ := different_block_pole_divisibility n i j W hj hji
  refine ⟨q.comp (CoefficientMapJet.shiftedVariable j), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (CoefficientMapJet.shiftedVariable j)) hq
  simpa only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, CoefficientMapJet.shiftedVariable, sub_add_cancel] using he

theorem full_candidate_matches_nine_jets (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    (X : ℚ[X]) ^ 9 ∣
      (weightedNumerator n W - partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) := by
  have hjmem : j ∈ range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hsplit : (partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) =
      (partialBlock n j W).comp (CoefficientMapJet.shiftedVariable j) +
        ∑ i ∈ (range (n + 1)).erase j,
          (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
    rw [partialNumerator_eq_sum_blocks, Polynomial.sum_comp]
    exact (Finset.add_sum_erase (range (n + 1))
      (fun i => (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j)) hjmem).symm
  have hoff : (X : ℚ[X]) ^ 9 ∣
      ∑ i ∈ (range (n + 1)).erase j,
        (partialBlock n i W).comp (CoefficientMapJet.shiftedVariable j) := by
    apply Finset.dvd_sum
    intro i hi
    exact different_block_shift_X_pow_dvd n i j W hj (Finset.ne_of_mem_erase hi).symm
  rw [Polynomial.sub_comp, hsplit, sub_add_eq_sub_sub]
  exact dvd_sub (own_block_matches_nine_jets n j W) hoff

theorem shifted_divisibility_implies_pole_divisibility (P : ℚ[X]) (j : ℕ)
    (h : (X : ℚ[X]) ^ 9 ∣ P.comp (CoefficientMapJet.shiftedVariable j)) :
    (X + C (j : ℚ)) ^ 9 ∣ P := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
  simpa only [Polynomial.comp_assoc, CoefficientMapJet.shiftedVariable,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
    Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he

theorem denominator_divides_actual_candidate_difference (n : ℕ) (W : ℚ[X]) :
    polePolynomial n ^ 9 ∣ weightedNumerator n W - partialNumerator n W := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    apply shifted_divisibility_implies_pole_divisibility
    exact full_candidate_matches_nine_jets n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem clearedPolePolynomial_natDegree (n j : ℕ) (hj : j ≤ n) :
    (clearedPolePolynomial n j).natDegree = n := by
  unfold clearedPolePolynomial
  rw [Polynomial.natDegree_prod_of_monic ((range (n + 1)).erase j)
    (fun k : ℕ => X + C (k : ℚ)) (fun k hk => Polynomial.monic_X_add_C (k : ℚ))]
  simp only [Polynomial.natDegree_X_add_C]
  simp [Nat.lt_succ_of_le hj]

theorem localTruncation_natDegree_le (n j : ℕ) (W : ℚ[X]) :
    (localTruncation n j W).natDegree ≤ 8 := by
  have h := PowerSeries.natDegree_trunc_lt (CoefficientMapJet.weightedClearedSeries n j W) 8
  exact Nat.le_of_lt_succ h

theorem partialBlock_natDegree_le (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    (partialBlock n j W).natDegree ≤ 9 * n + 8 := by
  have hm := Polynomial.natDegree_mul_le (p := clearedPolePolynomial n j ^ 9)
    (q := (localTruncation n j W).comp (X + C (j : ℚ)))
  have hc := Polynomial.natDegree_comp_le (p := localTruncation n j W) (q := X + C (j : ℚ))
  rw [Polynomial.natDegree_X_add_C, mul_one] at hc
  rw [Polynomial.natDegree_pow, clearedPolePolynomial_natDegree n j hj] at hm
  have ht := localTruncation_natDegree_le n j W
  unfold partialBlock
  omega

theorem partialNumerator_natDegree_le (n : ℕ) (W : ℚ[X]) :
    (partialNumerator n W).natDegree ≤ 9 * n + 8 := by
  rw [partialNumerator_eq_sum_blocks]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact partialBlock_natDegree_le n j W (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem actual_global_polynomial_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) : weightedNumerator n W = partialNumerator n W := by
  have hdvd := denominator_divides_actual_candidate_difference n W
  have hzero : weightedNumerator n W - partialNumerator n W = 0 := by
    by_contra hne
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hne
    rw [polePolynomial_pow_natDegree] at hdeg
    have hw := weightedNumerator_natDegree_le n W
    have hp := partialNumerator_natDegree_le n W
    have hdiff := Polynomial.natDegree_sub_le (weightedNumerator n W) (partialNumerator n W)
    unfold ProperMultiplier at hproper
    rcases le_total (weightedNumerator n W).natDegree (partialNumerator n W).natDegree with h | h
    · rw [max_eq_right h] at hdiff
      omega
    · rw [max_eq_left h] at hdiff
      omega
  exact sub_eq_zero.mp hzero

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

theorem actual_weighted_rational_representation (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    CoefficientMap.weightedR n W t =
      (weightedNumerator n W).eval t / ((polePolynomial n).eval t) ^ 9 := by
  simp only [weightedNumerator, Polynomial.eval_mul, Polynomial.eval_comp,
    baseNumerator_eval, baseU, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
    polePolynomial_eval, CoefficientMap.weightedR, CoefficientMap.actualR]
  ring

theorem partial_term_division (n j s : ℕ) (W : ℚ[X]) (t : ℚ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (CoefficientMapJet.weightedLocalCoefficient n j s W *
      (clearedPolePolynomial n j).eval t ^ 9 * (t + (j : ℚ)) ^ (9 - s)) /
        (polePolynomial n).eval t ^ 9 =
      CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff (pow_ne_zero _ (polePolynomial_eval_ne_zero n t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [polePolynomial_eval_factor n j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = CoefficientMapJet.weightedLocalCoefficient n j s W *
        (clearedPolePolynomial n j).eval t ^ 9 *
        ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem actual_global_partial_fractions (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  rw [actual_weighted_rational_representation, actual_global_polynomial_partial_fractions n W hproper]
  simp only [partialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact partial_term_division n j s W t (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular

end ZetaNine.CoefficientMapPartialFractions

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial
open CoefficientMapInjectivity CoefficientMapPartialFractions

theorem product_reverse_erased_range (n j : ℕ) (hj : j ≤ n) (f : ℕ → ℚ[X]) :
    ∏ k ∈ (range (n + 1)).erase (n - j), f (n - k) =
      ∏ k ∈ (range (n + 1)).erase j, f k := by
  apply Finset.prod_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
  · intro k hk
    have h := Finset.mem_erase.mp hk
    have hr := Finset.mem_range.mp h.2
    rw [Finset.mem_erase, Finset.mem_range]
    constructor <;> omega
  · intro k hk
    have h := Finset.mem_erase.mp hk
    have hr := Finset.mem_range.mp h.2
    rw [Finset.mem_erase, Finset.mem_range]
    constructor <;> omega
  · intro k hk
    have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    omega
  · intro k hk
    have h := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
    omega
  · intro k hk
    rfl

theorem sum_reverse_range (n : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ range (n + 1), f (n - k) = ∑ k ∈ range (n + 1), f k := by
  apply Finset.sum_nbij' (fun k : ℕ => n - k) (fun k : ℕ => n - k)
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    rw [Finset.mem_range]
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    have h := Finset.mem_range.mp hk
    omega
  · intro k hk
    rfl

theorem baseNumerator_reflection (n : ℕ) :
    (baseNumerator n).comp (reflectionVariable n) = baseNumerator n := by
  have hleft : (∏ i ∈ range n, (reflectionVariable n - C ((i : ℚ) + 1))) =
      (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
    calc
      _ = ∏ i ∈ range n, -(X + C (n : ℚ) + C ((i : ℚ) + 1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        unfold reflectionVariable
        ring
      _ = _ := by rw [Finset.prod_neg, Finset.card_range]
  have hright : (∏ i ∈ range n, (reflectionVariable n + C (n : ℚ) + C ((i : ℚ) + 1))) =
      (-1 : ℚ[X]) ^ n * ∏ i ∈ range n, (X - C ((i : ℚ) + 1)) := by
    calc
      _ = ∏ i ∈ range n, -(X - C ((i : ℚ) + 1)) := by
        apply Finset.prod_congr rfl
        intro i hi
        unfold reflectionVariable
        ring
      _ = _ := by rw [Finset.prod_neg, Finset.card_range]
  simp only [baseNumerator, Polynomial.mul_comp, Polynomial.prod_comp, Polynomial.C_comp,
    Polynomial.sub_comp, Polynomial.add_comp, Polynomial.X_comp]
  rw [hleft, hright]
  have hsign : (-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = C ((n.factorial : ℚ) ^ 7) * ((-1 : ℚ[X]) ^ n * (-1 : ℚ[X]) ^ n) *
        (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
        (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1))) := by ring
    _ = _ := by rw [hsign, mul_one]

theorem baseU_reflection (n : ℕ) : (baseU n).comp (reflectionVariable n) = baseU n := by
  simp only [baseU, Polynomial.mul_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
    reflectionVariable]
  ring

theorem weightedNumerator_reflection (n : ℕ) (W : ℚ[X]) :
    (weightedNumerator n W).comp (reflectionVariable n) = weightedNumerator n W := by
  simp only [weightedNumerator, Polynomial.mul_comp, baseNumerator_reflection,
    Polynomial.comp_assoc, baseU_reflection]

theorem clearedPolePolynomial_reflection (n j : ℕ) (hj : j ≤ n) :
    (clearedPolePolynomial n (n - j)).comp (reflectionVariable n) =
      C ((-1 : ℚ) ^ n) * clearedPolePolynomial n j := by
  simp only [clearedPolePolynomial, Polynomial.prod_comp, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp]
  calc
    _ = ∏ k ∈ (range (n + 1)).erase (n - j), -(X + C ((n - k : ℕ) : ℚ)) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hk' := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hk).2)
      rw [Nat.cast_sub hk', map_sub]
      unfold reflectionVariable
      ring
    _ = (-1 : ℚ[X]) ^ n * ∏ k ∈ (range (n + 1)).erase j, (X + C (k : ℚ)) := by
      rw [Finset.prod_neg,
        product_reverse_erased_range n j hj (fun k : ℕ => (X : ℚ[X]) + C (k : ℚ))]
      congr 1
      simp [Nat.lt_succ_of_le (Nat.sub_le n j)]
    _ = _ := by simp only [map_pow, map_neg, map_one]

theorem local_shift_reflection (n j : ℕ) (hj : j ≤ n) :
    (CoefficientMapJet.shiftedVariable (n - j)).comp (-X) =
      (reflectionVariable n).comp (CoefficientMapJet.shiftedVariable j) := by
  simp only [CoefficientMapJet.shiftedVariable, reflectionVariable, Polynomial.sub_comp,
    Polynomial.neg_comp, Polynomial.X_comp, Polynomial.C_comp, Nat.cast_sub hj, map_sub]
  ring

theorem shiftedWeightedNumerator_reflection (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n) :
    ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable (n - j))).comp (-X) =
      (weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) := by
  rw [Polynomial.comp_assoc, local_shift_reflection n j hj, ← Polynomial.comp_assoc,
    weightedNumerator_reflection]

theorem shiftedClearedDenominator_reflection (n j : ℕ) (hj : j ≤ n) :
    (CoefficientMapJet.shiftedClearedDenominator n (n - j)).comp (-X) =
      C ((-1 : ℚ) ^ n) * CoefficientMapJet.shiftedClearedDenominator n j := by
  rw [← clearedPolePolynomial_comp_shift, Polynomial.comp_assoc, local_shift_reflection n j hj,
    ← Polynomial.comp_assoc, clearedPolePolynomial_reflection n j hj,
    Polynomial.mul_comp, Polynomial.C_comp, clearedPolePolynomial_comp_shift]

theorem rescale_neg_one_C (a : ℚ) :
    PowerSeries.rescale (-1 : ℚ) (PowerSeries.C a) = PowerSeries.C a := by
  ext k
  by_cases hk : k = 0 <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hk]

theorem rescale_neg_one_polynomial (P : ℚ[X]) :
    PowerSeries.rescale (-1 : ℚ) (P : PowerSeries ℚ) = (P.comp (-X) : PowerSeries ℚ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [Polynomial.coe_add, map_add, hP, hQ, Polynomial.add_comp]
  | monomial k a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, Polynomial.coe_X,
        map_mul, map_pow, rescale_neg_one_C, PowerSeries.rescale_neg_one_X,
        Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp,
        Polynomial.coe_neg]

theorem actual_local_series_reflection (n j : ℕ) (hn : Even n) (W : ℚ[X]) (hj : j ≤ n) :
    PowerSeries.rescale (-1 : ℚ) (CoefficientMapJet.weightedClearedSeries n (n - j) W) =
      CoefficientMapJet.weightedClearedSeries n j W := by
  have hD : PowerSeries.rescale (-1 : ℚ)
      (CoefficientMapJet.shiftedClearedDenominator n (n - j) : PowerSeries ℚ) =
      (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) := by
    rw [rescale_neg_one_polynomial, shiftedClearedDenominator_reflection n j hj, hn.neg_one_pow]
    simp
  have hP : PowerSeries.rescale (-1 : ℚ)
      ((CoefficientMapJet.shiftedNumerator n (n - j) *
        W.comp (CoefficientMapJet.localU n (n - j)) : ℚ[X]) : PowerSeries ℚ) =
      ((CoefficientMapJet.shiftedNumerator n j * W.comp (CoefficientMapJet.localU n j) : ℚ[X]) : PowerSeries ℚ) := by
    rw [rescale_neg_one_polynomial, ← weightedNumerator_shift, shiftedWeightedNumerator_reflection n j W hj,
      weightedNumerator_shift]
  have he := congrArg (PowerSeries.rescale (-1 : ℚ))
    (CoefficientMapJet.weightedClearedSeries_denominator_identity n (n - j) W)
  rw [map_mul, map_pow, hD, hP] at he
  have hnonzero : (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 ≠ 0 := by
    intro hz
    have hc := pow_ne_zero 9 (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero n j)
    apply hc
    rw [← map_pow, hz, map_zero]
  apply mul_right_cancel₀ hnonzero
  exact he.trans (CoefficientMapJet.weightedClearedSeries_denominator_identity n j W).symm

theorem local_coefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    CoefficientMapJet.weightedLocalCoefficient n (n - j) s W =
      (-1 : ℚ) ^ (s + 1) * CoefficientMapJet.weightedLocalCoefficient n j s W := by
  have he := congrArg (PowerSeries.coeff (9 - s)) (actual_local_series_reflection n j hn W hj)
  rw [PowerSeries.coeff_rescale] at he
  have hsign : (-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s) = 1 := by
    rw [← mul_pow]
    norm_num
  have hparity : (-1 : ℚ) ^ (9 - s) = (-1 : ℚ) ^ (s + 1) := by
    interval_cases s <;> norm_num
  unfold CoefficientMapJet.weightedLocalCoefficient
  calc
    _ = ((-1 : ℚ) ^ (9 - s) * (-1 : ℚ) ^ (9 - s)) *
        PowerSeries.coeff (9 - s) (CoefficientMapJet.weightedClearedSeries n (n - j) W) := by rw [hsign, one_mul]
    _ = (-1 : ℚ) ^ (9 - s) *
        (((-1 : ℚ) ^ (9 - s)) *
          PowerSeries.coeff (9 - s) (CoefficientMapJet.weightedClearedSeries n (n - j) W)) := by ring
    _ = _ := by rw [he, hparity]

theorem rho_even_order_zero (n s : ℕ) (hn : Even n) (W : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hs : Even s) : rho n s W = 0 := by
  have he : rho n s W = (-1 : ℚ) ^ (s + 1) * rho n s W := by
    calc
      _ = ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n (n - j) s W :=
        (sum_reverse_range n _).symm
      _ = ∑ j ∈ range (n + 1), (-1 : ℚ) ^ (s + 1) *
          CoefficientMapJet.weightedLocalCoefficient n j s W := by
        apply Finset.sum_congr rfl
        intro j hj
        exact local_coefficient_reflection n j s hn W (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hs1 hs9
      _ = _ := by rw [← Finset.mul_sum]; rfl
  rw [pow_succ, hs.neg_one_pow, one_mul, neg_one_mul] at he
  linarith

theorem strong_proper_implies_proper (n : ℕ) (W : ℚ[X])
    (h : StrongProperMultiplier n W) : ProperMultiplier n W := by
  unfold StrongProperMultiplier at h
  unfold ProperMultiplier
  omega

theorem quartic_is_strong_proper (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    StrongProperMultiplier n W := by
  unfold StrongProperMultiplier
  omega

theorem clearedPolePolynomial_monic (n j : ℕ) : (clearedPolePolynomial n j).Monic := by
  unfold clearedPolePolynomial
  apply Polynomial.monic_prod_of_monic
  intro k hk
  exact Polynomial.monic_X_add_C _

theorem partialBasis_monic (n j s : ℕ) : (partialBasis n j s).Monic := by
  exact ((clearedPolePolynomial_monic n j).pow 9).mul ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s))

theorem partialBasis_natDegree (n j s : ℕ) (hj : j ≤ n) :
    (partialBasis n j s).natDegree = 9 * n + (9 - s) := by
  unfold partialBasis
  rw [Polynomial.natDegree_mul ((clearedPolePolynomial_monic n j).pow 9).ne_zero
    ((Polynomial.monic_X_add_C (j : ℚ)).pow (9 - s)).ne_zero,
    Polynomial.natDegree_pow, Polynomial.natDegree_pow,
    clearedPolePolynomial_natDegree n j hj, Polynomial.natDegree_X_add_C]
  omega

theorem partialBasis_simple_pole_top_coefficient (n j : ℕ) (hj : j ≤ n) :
    (partialBasis n j 1).coeff (9 * n + 8) = 1 := by
  have h := (partialBasis_monic n j 1).coeff_natDegree
  simpa only [partialBasis_natDegree n j 1 hj, Nat.reduceSub] using h

theorem partialBasis_higher_pole_top_coefficient (n j s : ℕ) (hj : j ≤ n)
    (hs : 2 ≤ s) (hs9 : s ≤ 9) : (partialBasis n j s).coeff (9 * n + 8) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [partialBasis_natDegree n j s hj]
  omega

theorem partialNumerator_top_coefficient_is_rho_one (n : ℕ) (W : ℚ[X]) :
    (partialNumerator n W).coeff (9 * n + 8) = rho n 1 W := by
  simp only [partialNumerator, Polynomial.finsetSum_coeff, rho]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [Finset.sum_eq_single_of_mem 1 (by simp)]
  · rw [mul_assoc, Polynomial.coeff_C_mul]
    change CoefficientMapJet.weightedLocalCoefficient n j 1 W *
      (partialBasis n j 1).coeff (9 * n + 8) = _
    rw [partialBasis_simple_pole_top_coefficient n j hj', mul_one]
  · intro s hs hsne
    have hs' := Finset.mem_Icc.mp hs
    have hs2 : 2 ≤ s := by omega
    rw [mul_assoc, Polynomial.coeff_C_mul]
    change CoefficientMapJet.weightedLocalCoefficient n j s W *
      (partialBasis n j s).coeff (9 * n + 8) = 0
    rw [partialBasis_higher_pole_top_coefficient n j s hj' hs2 hs'.2, mul_zero]

theorem rho_one_zero_of_strong_proper (n : ℕ) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : rho n 1 W = 0 := by
  have hpoly := actual_global_polynomial_partial_fractions n W (strong_proper_implies_proper n W hstrong)
  have hcoeff := congrArg (fun P : ℚ[X] => P.coeff (9 * n + 8)) hpoly
  rw [partialNumerator_top_coefficient_is_rho_one] at hcoeff
  have hzero : (weightedNumerator n W).coeff (9 * n + 8) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hbound := weightedNumerator_natDegree_le n W
    unfold StrongProperMultiplier at hstrong
    omega
  rw [hzero] at hcoeff
  exact hcoeff.symm

theorem original_integer_quartic_strong_proper (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) : StrongProperMultiplier n (W.map (Int.castRingHom ℚ)) := by
  exact quartic_is_strong_proper n (by omega) _ (le_trans Polynomial.natDegree_map_le hW)

end ZetaNine.CoefficientMapReflection

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open scoped BigOperators
open Finset Polynomial
open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions

theorem harmonicPower_succ (s T : ℕ) :
    harmonicPower s (T + 1) = harmonicPower s T + 1 / ((T + 1 : ℕ) : ℚ) ^ s := by
  unfold harmonicPower
  exact Finset.sum_Icc_succ_top (by omega) _

theorem shifted_harmonic_sum (s T j : ℕ) :
    (∑ t ∈ Icc 1 T, 1 / ((t : ℚ) + (j : ℚ)) ^ s) =
      harmonicPower s (T + j) - harmonicPower s j := by
  induction T with
  | zero => simp [harmonicPower]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have he : T + 1 + j = (T + j) + 1 := by omega
    rw [he, harmonicPower_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem actual_finite_harmonic_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      CoefficientMapJet.weightedLocalCoefficient n j s W *
        (harmonicPower s (T + j) - harmonicPower s j) := by
  unfold finiteL
  calc
    _ = ∑ t ∈ Icc 1 T, ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro t ht
      apply actual_global_partial_fractions n W hproper
      intro k hk
      have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
      exact ne_of_gt (add_pos_of_pos_of_nonneg htpos (Nat.cast_nonneg k))
    _ = ∑ j ∈ range (n + 1), ∑ t ∈ Icc 1 T, ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s :=
      Finset.sum_comm
    _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ∑ t ∈ Icc 1 T,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      have hterm : (∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s) =
          ∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W * (1 / ((t : ℚ) + (j : ℚ)) ^ s) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rw [hterm]
      rw [← Finset.mul_sum, shifted_harmonic_sum]

theorem actual_grouped_finite_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_finite_harmonic_identity n T W hproper]
  have hmain : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s T := by
    unfold rho
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  rw [hmain]
  unfold constantTerm shiftedTail
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem actual_grouped_finite_identity_no_simple_pole (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hcancel : rho n 1 W = 0) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_grouped_finite_identity n T W hproper]
  have hsplit : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      rho n 1 W * harmonicPower 1 T + ∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    rfl
  rw [hsplit, hcancel, zero_mul, zero_add]

theorem actual_grouped_finite_identity_odd (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (h1 : rho n 1 W = 0)
    (h2 : rho n 2 W = 0) (h4 : rho n 4 W = 0)
    (h6 : rho n 6 W = 0) (h8 : rho n 8 W = 0) :
    finiteL n T W = constantTerm n W +
      (rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
       rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T) +
      shiftedTail n T W := by
  rw [actual_grouped_finite_identity_no_simple_pole n T W hproper h1]
  have hs : (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) =
      rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
      rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T := by
    norm_num [Finset.sum_Icc_succ_top, h2, h4, h6, h8]
  rw [hs]

theorem harmonic_difference_eq_shifted (s T j : ℕ) :
    harmonicPower s (T + j) - harmonicPower s T =
      ∑ k ∈ Icc 1 j, 1 / ((T : ℚ) + (k : ℚ)) ^ s := by
  simpa only [Nat.add_comm j T, add_comm] using (shifted_harmonic_sum s j T).symm

end ZetaNine.CoefficientMapFiniteSum




/-!
Actual finite/infinite summation for p=9, q=1, m=n.
All cancellations come from the actual reflection and stronger degree theorem.
Any HasSum assertion must additionally use a proved Summable statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapSummation

open HarmonicStability CoefficientMapInjectivity CoefficientMapReflection







theorem actual_finite_odd_identity (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) :
    CoefficientMapFiniteSum.finiteL n T W = CoefficientMapFiniteSum.constantTerm n W +
      (CoefficientMapFiniteSum.rho n 3 W * harmonicPower 3 T +
       CoefficientMapFiniteSum.rho n 5 W * harmonicPower 5 T +
       CoefficientMapFiniteSum.rho n 7 W * harmonicPower 7 T +
       CoefficientMapFiniteSum.rho n 9 W * harmonicPower 9 T) +
      CoefficientMapFiniteSum.shiftedTail n T W := by
  exact CoefficientMapFiniteSum.actual_grouped_finite_identity_odd n T W
    (strong_proper_implies_proper n W hstrong) (rho_one_zero_of_strong_proper n W hstrong)
    (rho_even_order_zero n 2 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 4 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 6 hn W (by norm_num) (by norm_num) (by norm_num))
    (rho_even_order_zero n 8 hn W (by norm_num) (by norm_num) (by norm_num))

theorem sum_Icc_eq_sum_range_successor (T : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Icc 1 T, f t = ∑ t ∈ range T, f (t + 1) := by
  apply Finset.sum_nbij' (fun t : ℕ => t - 1) (fun t : ℕ => t + 1)
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    rw [Finset.mem_range]
    omega
  · intro t ht
    have h := Finset.mem_range.mp ht
    rw [Finset.mem_Icc]
    omega
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    omega
  · intro t ht
    omega
  · intro t ht
    have h := Finset.mem_Icc.mp ht
    have he : t - 1 + 1 = t := by omega
    rw [he]

theorem harmonicPower_cast (s T : ℕ) :
    (harmonicPower s T : ℝ) = ∑ t ∈ Icc 1 T, 1 / (t : ℝ) ^ s := by
  unfold harmonicPower
  push_cast
  rfl

theorem harmonicPower_cast_eq_range (s T : ℕ) (hs : 1 ≤ s) :
    (harmonicPower s T : ℝ) = ∑ t ∈ range (T + 1), 1 / (t : ℝ) ^ s := by
  rw [harmonicPower_cast, sum_Icc_eq_sum_range_successor, Finset.sum_range_succ']
  simp [show s ≠ 0 by omega]

theorem zetaReal_eq_tsum (s : ℕ) (hs : 1 < s) :
    zetaReal s = ∑' t : ℕ, 1 / (t : ℝ) ^ s := by
  have he : ((∑' t : ℕ, 1 / (t : ℝ) ^ s : ℝ) : ℂ) = riemannZeta (s : ℂ) := by
    rw [Complex.ofReal_tsum, zeta_nat_eq_tsum_of_gt_one hs]
    apply tsum_congr
    intro t
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_natCast]
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re, zetaReal] using hr.symm

theorem harmonicPower_tendsto_zeta (s : ℕ) (hs : 1 < s) :
    Tendsto (fun T : ℕ => (harmonicPower s T : ℝ)) atTop (𝓝 (zetaReal s)) := by
  have h := ((Real.summable_one_div_nat_pow.mpr hs).hasSum.tendsto_sum_nat).comp
    (tendsto_add_atTop_nat 1)
  rw [← zetaReal_eq_tsum s hs] at h
  simpa only [Function.comp_def, ← harmonicPower_cast_eq_range s _ (by omega)] using h

theorem shifted_reciprocal_tendsto_zero (s k : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun T : ℕ => 1 / ((T : ℝ) + (k : ℝ)) ^ s) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℕ => (((T + k : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat k))
  simpa only [one_div, inv_pow, Nat.cast_add, zero_pow (show s ≠ 0 by omega)] using hbase.pow s

theorem harmonic_fixed_tail_tendsto_zero (s j : ℕ) (hs : 1 ≤ s) :
    Tendsto (fun T : ℕ => ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Icc 1 j) (fun k hk => shifted_reciprocal_tendsto_zero s k hs)
  have he : (fun T : ℕ => ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) =
      (fun T : ℕ => ∑ k ∈ Icc 1 j, 1 / ((T : ℝ) + (k : ℝ)) ^ s) := by
    funext T
    rw [CoefficientMapFiniteSum.harmonic_difference_eq_shifted]
    push_cast
    rfl
  rw [he]
  simpa only [Finset.sum_const_zero] using h

theorem actual_shiftedTail_tendsto_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range (n + 1)) (fun j hj =>
    tendsto_finsetSum (Icc 1 9) (fun s hs =>
      (harmonic_fixed_tail_tendsto_zero s j (Finset.mem_Icc.mp hs).1).const_mul
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ)))
  have he : (fun T : ℕ => (CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) =
      (fun T : ℕ => ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) *
          ((harmonicPower s (T + j) - harmonicPower s T : ℚ) : ℝ)) := by
    funext T
    unfold CoefficientMapFiniteSum.shiftedTail
    push_cast
    rfl
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

theorem actual_finiteL_tendsto_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) :
    Tendsto (fun T : ℕ => (CoefficientMapFiniteSum.finiteL n T W : ℝ)) atTop (𝓝 (exactL n W)) := by
  have hB : Tendsto (fun _ : ℕ => (CoefficientMapFiniteSum.constantTerm n W : ℝ)) atTop
      (𝓝 (CoefficientMapFiniteSum.constantTerm n W : ℝ)) := tendsto_const_nhds
  have hmain := (((harmonicPower_tendsto_zeta 3 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 3 W : ℝ)).add
    ((harmonicPower_tendsto_zeta 5 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 5 W : ℝ))).add
    ((harmonicPower_tendsto_zeta 7 (by omega)).const_mul (CoefficientMapFiniteSum.rho n 7 W : ℝ))
  have hmain' := hmain.add ((harmonicPower_tendsto_zeta 9 (by omega)).const_mul
    (CoefficientMapFiniteSum.rho n 9 W : ℝ))
  have h := (hB.add hmain').add (actual_shiftedTail_tendsto_zero n W)
  convert h using 1
  · funext T
    rw [actual_finite_odd_identity n T hn W hstrong]
    push_cast
    rfl
  · simp only [exactL, add_zero]

theorem simple_pole_difference_identity (t : ℝ) (ht : 0 < t) (j : ℕ) :
    1 / (t + (j : ℝ)) - 1 / t = -(j : ℝ) / (t * (t + (j : ℝ))) := by
  have hj : 0 < t + (j : ℝ) := add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg j)
  field_simp [ne_of_gt ht, ne_of_gt hj]
  ring

theorem simple_pole_difference_summable (j : ℕ) :
    Summable (fun t : ℕ => 1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1)) := by
  have hp := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
    (show Function.Injective (fun t : ℕ => t + 1) from fun a b h => by dsimp at h; omega)
  have hmajorant : Summable (fun t : ℕ => (j : ℝ) * (1 / ((t : ℝ) + 1) ^ 2)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hp.mul_left (j : ℝ)
  apply Summable.of_norm_bounded hmajorant
  intro t
  have ht : 0 < (t : ℝ) + 1 := by positivity
  have hj : 0 < (t : ℝ) + 1 + (j : ℝ) := by positivity
  rw [simple_pole_difference_identity _ ht j, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg j), abs_of_pos (mul_pos ht hj)]
  have hden : ((t : ℝ) + 1) ^ 2 ≤ ((t : ℝ) + 1) * ((t : ℝ) + 1 + (j : ℝ)) := by
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  calc
    _ ≤ (j : ℝ) / ((t : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg j) (pow_pos ht 2) hden
    _ = _ := by ring

theorem shifted_high_order_summable (j s : ℕ) (hs : 2 ≤ s) :
    Summable (fun t : ℕ => 1 / ((t : ℝ) + 1 + (j : ℝ)) ^ s) := by
  have hp := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s)).comp_injective
    (show Function.Injective (fun t : ℕ => t + 1 + j) from fun a b h => by dsimp at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hp

theorem actualSeries_eq_principal_parts (n : ℕ) (W : ℚ[X]) (hproper : ProperMultiplier n W) (t : ℕ) :
    actualSeries n W t = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
  unfold actualSeries
  rw [CoefficientMapPartialFractions.actual_global_partial_fractions n W hproper]
  · push_cast
    rfl
  · intro k hk
    have ht : (0 : ℚ) < ((t + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos t
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht (Nat.cast_nonneg k))

theorem actualSeries_eq_cancelled_principal_parts (n : ℕ) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (t : ℕ) :
    actualSeries n W t =
      (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
        (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) +
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 2 9,
        (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
  have hzero : (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ)) = 0 := by
    have h := rho_one_zero_of_strong_proper n W hstrong
    unfold rho at h
    exact_mod_cast h
  have hcorrection : (∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
      (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) =
      ∑ j ∈ range (n + 1), (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
        ((t : ℝ) + 1 + (j : ℝ)) := by
    calc
      _ = ∑ j ∈ range (n + 1), ((CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
          ((t : ℝ) + 1 + (j : ℝ)) - (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) /
          ((t : ℝ) + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_div, hzero, zero_div, sub_zero]
  rw [actualSeries_eq_principal_parts n W (strong_proper_implies_proper n W hstrong) t, hcorrection]
  have hsplit (j : ℕ) : (∑ s ∈ Icc 1 9, (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) /
      ((t : ℝ) + 1 + (j : ℝ)) ^ s) =
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) +
        ∑ s ∈ Icc 2 9, (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) /
          ((t : ℝ) + 1 + (j : ℝ)) ^ s := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    simp only [pow_one, Nat.reduceAdd]
    rw [show (Ico 2 10 : Finset ℕ) = Icc 2 9 by decide]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]

theorem actualSeries_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (actualSeries n W) := by
  have hsimple : Summable (fun t : ℕ => ∑ j ∈ range (n + 1),
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ) *
        (1 / ((t : ℝ) + 1 + (j : ℝ)) - 1 / ((t : ℝ) + 1))) :=
    summable_sum (fun j hj => (simple_pole_difference_summable j).mul_left
      (CoefficientMapJet.weightedLocalCoefficient n j 1 W : ℝ))
  have hhigher : Summable (fun t : ℕ => ∑ j ∈ range (n + 1), ∑ s ∈ Icc 2 9,
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ) / ((t : ℝ) + 1 + (j : ℝ)) ^ s) := by
    apply summable_sum
    intro j hj
    apply summable_sum
    intro s hs
    simpa only [mul_one_div] using (shifted_high_order_summable j s (Finset.mem_Icc.mp hs).1).mul_left
      (CoefficientMapJet.weightedLocalCoefficient n j s W : ℝ)
  exact (hsimple.add hhigher).congr (fun t => (actualSeries_eq_cancelled_principal_parts n W hstrong t).symm)

theorem checked_actualSeries_norm_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (fun t : ℕ => ‖actualSeries n W t‖) := (actualSeries_summable n W hstrong).norm

theorem actualSeries_partial_sums (n T : ℕ) (W : ℚ[X]) :
    (∑ t ∈ range T, actualSeries n W t) = (CoefficientMapFiniteSum.finiteL n T W : ℝ) := by
  symm
  unfold CoefficientMapFiniteSum.finiteL
  push_cast
  exact sum_Icc_eq_sum_range_successor T (fun t : ℕ => (CoefficientMap.weightedR n W (t : ℚ) : ℝ))

theorem actualSeries_hasSum_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : HasSum (actualSeries n W) (exactL n W) := by
  have hsum := actualSeries_summable n W hstrong
  have hlimit : Tendsto (fun T : ℕ => ∑ t ∈ range T, actualSeries n W t) atTop (𝓝 (exactL n W)) := by
    simpa only [actualSeries_partial_sums] using actual_finiteL_tendsto_exactL n hn W hstrong
  have he : (∑' t : ℕ, actualSeries n W t) = exactL n W :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hlimit
  simpa only [he] using hsum.hasSum

theorem actualSeries_tsum_exactL (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) : (∑' t : ℕ, actualSeries n W t) = exactL n W :=
  (actualSeries_hasSum_exactL n hn W hstrong).tsum_eq

theorem original_integer_quartic_exact_infinite_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    HasSum (actualSeries n (W.map (Int.castRingHom ℚ))) (exactL n (W.map (Int.castRingHom ℚ))) :=
  actualSeries_hasSum_exactL n hn _ (original_integer_quartic_strong_proper n hn2 hn W hW)

end ZetaNine.CoefficientMapSummation















open ZetaNine ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability

theorem solution (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
    Summable (fun t : ℕ => ‖actualSeries n W t‖) := by
  exact ZetaNine.CoefficientMapSummation.checked_actualSeries_norm_summable n W hstrong

#print axioms solution
