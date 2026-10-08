-- Prove2me | solution 1 for ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-04T11:09:31.685449+00:00
-- url     : https://prove2.me/submissions/55c39aff-8bc3-4cba-b117-bd340e8fa8c7

import Definitions.Def_ZetaNine_CoefficientMapKernelBridge
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMap

open scoped BigOperators
open Finset
open Polynomial

theorem poleProduct_ne_zero (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : poleProduct n t ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact ht k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

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

theorem baseNumerator_ne_zero (n : ℕ) : baseNumerator n ≠ 0 := by
  unfold baseNumerator
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Polynomial.C_ne_zero.mpr
      apply pow_ne_zero
      exact_mod_cast n.factorial_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact Polynomial.X_sub_C_ne_zero _
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [add_assoc, ← map_add]
    exact Polynomial.X_add_C_ne_zero _

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

theorem weightedNumerator_zero_implies_multiplier_zero (n : ℕ) (W : ℚ[X])
    (h : weightedNumerator n W = 0) : W = 0 := by
  have hcomp : W.comp (baseU n) = 0 :=
    (mul_eq_zero.mp h).resolve_left (baseNumerator_ne_zero n)
  rcases Polynomial.comp_eq_zero_iff.mp hcomp with hW | hconstant
  · exact hW
  · have hdeg := congrArg Polynomial.natDegree hconstant.2
    rw [baseU_natDegree, Polynomial.natDegree_C] at hdeg
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

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapSummation

open scoped BigOperators Topology
open Finset Polynomial Filter
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

theorem actualSeries_norm_summable (n : ℕ) (W : ℚ[X]) (hstrong : StrongProperMultiplier n W) :
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

end ZetaNine.CoefficientMapSummation

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapAggregate

open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection

theorem actual_local_coefficient_add (n j s : ℕ) (W V : ℚ[X]) :
    weightedLocalCoefficient n j s (W + V) =
      weightedLocalCoefficient n j s W + weightedLocalCoefficient n j s V := by
  simp [weightedLocalCoefficient, weightedClearedSeries, add_comp, mul_add]

theorem actual_local_coefficient_smul (n j s : ℕ) (a : ℚ) (W : ℚ[X]) :
    weightedLocalCoefficient n j s (a • W) = a * weightedLocalCoefficient n j s W := by
  simp [weightedLocalCoefficient, weightedClearedSeries, smul_comp, smul_eq_mul]

theorem actual_rho_add (n s : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (W + V) =
      CoefficientMapFiniteSum.rho n s W + CoefficientMapFiniteSum.rho n s V := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_add, Finset.sum_add_distrib]

theorem actual_rho_smul (n s : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.rho n s (a • W) = a * CoefficientMapFiniteSum.rho n s W := by
  simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_smul, Finset.mul_sum]

theorem actual_constant_add (n : ℕ) (W V : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (W + V) =
      CoefficientMapFiniteSum.constantTerm n W + CoefficientMapFiniteSum.constantTerm n V := by
  simp only [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem actual_constant_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    CoefficientMapFiniteSum.constantTerm n (a • W) = a * CoefficientMapFiniteSum.constantTerm n W := by
  simp [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_smul, mul_assoc,
    Finset.mul_sum]

theorem aggregate_add (n : ℕ) (W V : ℚ[X]) :
    aggregate n (W + V) = aggregate n W + aggregate n V := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_add, actual_rho_add]

theorem aggregate_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
    aggregate n (a • W) = a • aggregate n W := by
  funext i
  fin_cases i <;> simp [aggregate, actual_constant_smul, actual_rho_smul, smul_eq_mul]

theorem coordinatePolynomial_add (a b : Fin 5 → ℚ) :
    coordinatePolynomial (a + b) = coordinatePolynomial a + coordinatePolynomial b := by
  simp [coordinatePolynomial, C_add, add_mul, Finset.sum_add_distrib]

theorem coordinatePolynomial_smul (c : ℚ) (a : Fin 5 → ℚ) :
    coordinatePolynomial (c • a) = c • coordinatePolynomial a := by
  simp [coordinatePolynomial, smul_eq_mul, C_mul, mul_assoc, smul_eq_C_mul,
    Finset.mul_sum]

theorem coordinatePolynomial_coeff (a : Fin 5 → ℚ) (i : Fin 5) :
    (coordinatePolynomial a).coeff i.val = a i := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have h : i.val ≠ j.val := by intro he; exact hji (Fin.ext he.symm)
    simp [h]
  · simp

theorem coordinatePolynomial_natDegree_le (a : Fin 5 → ℚ) :
    (coordinatePolynomial a).natDegree ≤ 4 := by
  unfold coordinatePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h : (C (a i) * X ^ i.val : ℚ[X]).natDegree ≤
      (C (a i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
  simp only [natDegree_C, natDegree_X_pow, zero_add] at h
  exact h.trans (by have := i.isLt; omega)

theorem coordinates_restore (a : Fin 5 → ℚ) :
    polynomialCoordinates (coordinatePolynomial a) = a := by
  funext i
  exact coordinatePolynomial_coeff a i

theorem coordinatePolynomial_injective : Function.Injective coordinatePolynomial := by
  intro a b hab
  simpa only [coordinates_restore] using congrArg polynomialCoordinates hab

theorem quartic_aggregate_is_actual (n : ℕ) (a : Fin 5 → ℚ) :
    quarticAggregateLinearMap n a = aggregate n (coordinatePolynomial a) := rfl

theorem aggregate_zero_iff (n : ℕ) (W : ℚ[X]) :
    aggregate n W = 0 ↔ CoefficientMapFiniteSum.constantTerm n W = 0 ∧
      CoefficientMapFiniteSum.rho n 3 W = 0 ∧ CoefficientMapFiniteSum.rho n 5 W = 0 ∧
      CoefficientMapFiniteSum.rho n 7 W = 0 ∧ CoefficientMapFiniteSum.rho n 9 W = 0 := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3, congrFun h 4⟩
  · rintro ⟨hB, h3, h5, h7, h9⟩
    funext i
    fin_cases i <;> simp [aggregate, hB, h3, h5, h7, h9]

theorem aggregate_zero_all_rho (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : CoefficientMapFiniteSum.rho n s W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  have h1 : CoefficientMapFiniteSum.rho n 1 W = 0 := rho_one_zero_of_strong_proper n W hstrong
  have h2 : CoefficientMapFiniteSum.rho n 2 W = 0 := rho_even_order_zero n 2 hn W (by omega) (by omega) (by norm_num)
  have h4 : CoefficientMapFiniteSum.rho n 4 W = 0 := rho_even_order_zero n 4 hn W (by omega) (by omega) (by norm_num)
  have h6 : CoefficientMapFiniteSum.rho n 6 W = 0 := rho_even_order_zero n 6 hn W (by omega) (by omega) (by norm_num)
  have h8 : CoefficientMapFiniteSum.rho n 8 W = 0 := rho_even_order_zero n 8 hn W (by omega) (by omega) (by norm_num)
  interval_cases s <;> assumption

theorem aggregate_zero_exactL (n : ℕ) (W : ℚ[X]) (hzero : aggregate n W = 0) :
    CoefficientMapSummation.exactL n W = 0 := by
  obtain ⟨hB, h3, h5, h7, h9⟩ := (aggregate_zero_iff n W).mp hzero
  simp [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9]

end ZetaNine.CoefficientMapAggregate

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapTelescoper

open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate

theorem prefixSum_succ (c : ℕ → ℚ) (j : ℕ) :
    prefixSum c (j + 1) = prefixSum c j + c (j + 1) := by
  unfold prefixSum
  exact Finset.sum_range_succ _ _

theorem finite_cumulative_difference (n : ℕ) (c f : ℕ → ℚ) :
    (∑ j ∈ range n, prefixSum c j * (f j - f (j + 1))) =
      (∑ j ∈ range (n + 1), c j * f j) - prefixSum c n * f n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => prefixSum c j * (f j - f (j + 1))) n, ih,
      Finset.sum_range_succ (fun j => c j * f j) (n + 1), prefixSum_succ]
    ring

theorem cumulativeCoefficient_succ (n j s : ℕ) (W : ℚ[X]) :
    cumulativeCoefficient n (j + 1) s W = cumulativeCoefficient n j s W +
      weightedLocalCoefficient n (j + 1) s W := prefixSum_succ _ j

theorem cumulativeCoefficient_last_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : cumulativeCoefficient n n s W = 0 :=
  aggregate_zero_all_rho n hn W hstrong hzero s hs1 hs9

theorem telescoper_as_sum_over_orders (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    telescoper n W t = ∑ s ∈ Icc 1 9, ∑ j ∈ range n,
      cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s := Finset.sum_comm

theorem telescoper_difference_principal_parts (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W t - telescoper n W (t + 1) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  rw [telescoper_as_sum_over_orders, telescoper_as_sum_over_orders, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range n, cumulativeCoefficient n j s W *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hshift : (t + 1) + (j : ℚ) = t + ((j + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hshift]
      ring
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      have h := finite_cumulative_difference n (fun j => weightedLocalCoefficient n j s W)
        (fun j => 1 / (t + (j : ℚ)) ^ s)
      change (∑ j ∈ range n, prefixSum (fun j => weightedLocalCoefficient n j s W) j *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s)) = _
      rw [h]
      have htotal : prefixSum (fun j => weightedLocalCoefficient n j s W) n = 0 :=
        cumulativeCoefficient_last_zero n hn W hstrong hzero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
      simp only [htotal, mul_one_div, zero_div, sub_zero]
    _ = _ := Finset.sum_comm

theorem actual_weightedR_is_difference (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t = telescoper n W t - telescoper n W (t + 1) := by
  rw [telescoper_difference_principal_parts n hn W hstrong hzero t]
  exact CoefficientMapPartialFractions.actual_global_partial_fractions n W
    (strong_proper_implies_proper n W hstrong) t hregular

theorem telescoper_positive_tendsto_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range n) (fun j hj => tendsto_finsetSum (Icc 1 9) (fun s hs =>
    (CoefficientMapSummation.shifted_reciprocal_tendsto_zero s (j + 1) (Finset.mem_Icc.mp hs).1).const_mul
      (cumulativeCoefficient n j s W : ℝ)))
  have he : (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) =
      (fun T : ℕ => ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
        (cumulativeCoefficient n j s W : ℝ) * (1 / ((T : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ s)) := by
    funext T
    unfold telescoper
    push_cast
    simp only [mul_one_div, add_left_comm, add_comm]
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

theorem finite_sum_is_telescoper_boundary (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    CoefficientMapFiniteSum.finiteL n T W = telescoper n W 1 - telescoper n W ((T + 1 : ℕ) : ℚ) := by
  induction T with
  | zero => simp [CoefficientMapFiniteSum.finiteL]
  | succ T ih =>
    have hstep : CoefficientMapFiniteSum.finiteL n (T + 1) W =
        CoefficientMapFiniteSum.finiteL n T W + CoefficientMap.weightedR n W ((T + 1 : ℕ) : ℚ) := by
      unfold CoefficientMapFiniteSum.finiteL
      exact Finset.sum_Icc_succ_top (by omega) _
    rw [hstep, ih, actual_weightedR_is_difference n hn W hstrong hzero]
    · have he : ((T + 1 : ℕ) : ℚ) + 1 = ((T + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he]
      ring
    · intro k hk
      exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k))

theorem telescoper_at_one_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) : telescoper n W 1 = 0 := by
  have hfinite := CoefficientMapSummation.actual_finiteL_tendsto_exactL n hn W hstrong
  rw [aggregate_zero_exactL n W hzero] at hfinite
  have hboundary := (tendsto_const_nhds (x := (telescoper n W 1 : ℝ))).sub
    (telescoper_positive_tendsto_zero n W)
  have he : (fun T : ℕ => (CoefficientMapFiniteSum.finiteL n T W : ℝ)) =
      (fun T : ℕ => (telescoper n W 1 : ℝ) - (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) := by
    funext T
    rw [finite_sum_is_telescoper_boundary n T hn W hstrong hzero]
    push_cast
    rfl
  rw [he] at hfinite
  have h := tendsto_nhds_unique hfinite hboundary
  simp only [sub_zero] at h
  exact_mod_cast h.symm

theorem actual_weightedR_positive_zero (n k : ℕ) (W : ℚ[X]) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.weightedR n W (k : ℚ) = 0 := by
  have hprod : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show k - 1 < n by omega))
    have he : k - 1 + 1 = k := by omega
    exact sub_eq_zero.mpr (by exact_mod_cast he.symm)
  simp [CoefficientMap.weightedR, CoefficientMap.actualR, CoefficientMap.numerator, hprod]

theorem telescoper_positive_zeros (n k : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) : telescoper n W (k : ℚ) = 0 := by
  have hzeros : ∀ l ≤ n, telescoper n W ((l + 1 : ℕ) : ℚ) = 0 := by
    intro l
    induction l with
    | zero => intro hl; exact telescoper_at_one_zero n hn W hstrong hzero
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      have hdiff := actual_weightedR_is_difference n hn W hstrong hzero ((l + 1 : ℕ) : ℚ)
        (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k)))
      rw [actual_weightedR_positive_zero n (l + 1) W (by omega) (by omega), hprev] at hdiff
      have he : ((l + 1 : ℕ) : ℚ) + 1 = ((l + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he] at hdiff
      linarith
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using hzeros (k - 1) (by omega)

theorem cumulativeCoefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hj : j < n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    cumulativeCoefficient n (n - 1 - j) s W = (-1 : ℚ) ^ s * cumulativeCoefficient n j s W := by
  induction j with
  | zero =>
    have hn1 : 1 ≤ n := by omega
    have hlast := cumulativeCoefficient_last_zero n hn W hstrong hzero s hs1 hs9
    have hstep := cumulativeCoefficient_succ n (n - 1) s W
    rw [show n - 1 + 1 = n by omega, hlast] at hstep
    have hreflection := local_coefficient_reflection n 0 s hn W (by omega) hs1 hs9
    simp only [Nat.sub_zero, pow_succ] at hreflection
    simp only [Nat.sub_zero]
    have hfirst : cumulativeCoefficient n 0 s W = weightedLocalCoefficient n 0 s W := by
      simp [cumulativeCoefficient, prefixSum]
    rw [hfirst]
    rw [hreflection] at hstep
    nlinarith
  | succ j ih =>
    have hprev := ih (by omega)
    have hstep := cumulativeCoefficient_succ n (n - 1 - (j + 1)) s W
    rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega, hprev] at hstep
    have hreflection := local_coefficient_reflection n (j + 1) s hn W (by omega) hs1 hs9
    rw [show n - (j + 1) = n - 1 - j by omega] at hreflection
    rw [hreflection, pow_succ] at hstep
    rw [cumulativeCoefficient_succ]
    nlinarith

theorem telescoper_reflection (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W (1 - (n : ℚ) - t) = telescoper n W t := by
  have hreverse := sum_reverse_range (n - 1)
    (fun j => ∑ s ∈ Icc 1 9,
      cumulativeCoefficient n j s W / ((1 - (n : ℚ) - t) + (j : ℚ)) ^ s)
  rw [show n - 1 + 1 = n by omega] at hreverse
  unfold telescoper
  rw [← hreverse]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro s hs
  rw [cumulativeCoefficient_reflection n j s hn W hstrong hzero hjn
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  have he : (1 - (n : ℚ) - t) + ((n - 1 - j : ℕ) : ℚ) = -(t + (j : ℚ)) := by
    have hnsub : (n - 1 - j : ℕ) + (j + 1) = n := by omega
    have hc : ((n - 1 - j : ℕ) : ℚ) + ((j : ℚ) + 1) = (n : ℚ) := by exact_mod_cast hnsub
    linarith
  rw [he, neg_pow (t + (j : ℚ))]
  exact mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℚ) ≠ 0))

theorem telescoper_negative_zeros (n k : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (hk : k ≤ n) :
    telescoper n W (-(n : ℚ) - (k : ℚ)) = 0 := by
  have hreflection := telescoper_reflection n hn1 hn W hstrong hzero (-(n : ℚ) - (k : ℚ))
  have he : 1 - (n : ℚ) - (-(n : ℚ) - (k : ℚ)) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [he, telescoper_positive_zeros n (k + 1) hn W hstrong hzero (by omega) (by omega)] at hreflection
  exact hreflection.symm

theorem cleared_term_division (n j s : ℕ) (a t : ℚ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial n).eval t ^ 9 = a / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff
    (pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero n t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [CoefficientMapPartialFractions.polePolynomial_eval_factor n j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = (telescoperNumerator n W).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  symm
  simp only [telescoperNumerator, partialBasis, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [mul_assoc] using cleared_term_division (n - 1) j s (cumulativeCoefficient n j s W) t
    (by have := Finset.mem_range.mp hj; omega) (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    (by intro k hk; exact hregular k (by omega))

theorem telescoperNumerator_natDegree_le (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) :
    (telescoperNumerator n W).natDegree ≤ 9 * n - 1 := by
  unfold telescoperNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have h : (C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s).natDegree ≤
      (C (cumulativeCoefficient n j s W)).natDegree + (partialBasis (n - 1) j s).natDegree :=
    Polynomial.natDegree_mul_le
  rw [Polynomial.natDegree_C, zero_add,
    partialBasis_natDegree (n - 1) j s (by have := Finset.mem_range.mp hj; omega)] at h
  have horder := Finset.mem_Icc.mp hs
  omega

theorem rootNode_injective (n : ℕ) : Function.Injective (rootNode n) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simpa [rootNode] using h
      exact_mod_cast he
    | inr b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
  | inr a =>
    cases b with
    | inl b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
    | inr b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simp only [rootNode] at h; linarith
      exact_mod_cast he

theorem rootPolynomial_monic (n : ℕ) : (rootPolynomial n).Monic := by
  unfold rootPolynomial
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_sub_C _

theorem rootPolynomial_eq_explicit_products (n : ℕ) :
    rootPolynomial n =
      (∏ k ∈ range (n + 1), (X - C ((k : ℚ) + 1))) *
      (∏ k ∈ range (n + 1), (X + C (n : ℚ) + C (k : ℚ))) := by
  unfold rootPolynomial
  rw [Fintype.prod_sum_type]
  simp only [rootNode]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C ((k : ℚ) + 1) : ℚ[X])) (n + 1),
    Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C (-(n : ℚ) - (k : ℚ)) : ℚ[X])) (n + 1)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_sub, map_neg]
  ring

theorem rootPolynomial_natDegree (n : ℕ) : (rootPolynomial n).natDegree = 2 * n + 2 := by
  unfold rootPolynomial
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C]
  simp
  omega

theorem telescoperNumerator_zero_at_nodes (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) : (telescoperNumerator n W).eval (rootNode n i) = 0 := by
  have hregular : ∀ k < n, rootNode n i + (k : ℚ) ≠ 0 := by
    intro k hk
    cases i with
    | inl l =>
      simp only [rootNode]
      exact ne_of_gt (by positivity)
    | inr l =>
      simp only [rootNode]
      have hkn : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
      have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
      exact ne_of_lt (by linarith)
  have hvalue : telescoper n W (rootNode n i) = 0 := by
    cases i with
    | inl k =>
      simpa only [rootNode, Nat.cast_add, Nat.cast_one] using
        telescoper_positive_zeros n (k.val + 1) hn W hstrong hzero (by omega) (by have := k.isLt; omega)
    | inr k =>
      exact telescoper_negative_zeros n k.val hn1 hn W hstrong hzero (by have := k.isLt; omega)
  have hrep := telescoper_actual_rational_representation n hn1 W (rootNode n i) hregular
  have hden : (polePolynomial (n - 1)).eval (rootNode n i) ^ 9 ≠ 0 :=
    pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) _
      (by intro k hk; exact hregular k (by omega)))
  rw [hvalue] at hrep
  have hmult := congrArg (fun x : ℚ => x * (polePolynomial (n - 1)).eval (rootNode n i) ^ 9) hrep
  rw [div_mul_cancel₀ _ hden] at hmult
  simpa only [zero_mul] using hmult.symm

theorem all_kernel_nodes_divide_telescoperNumerator (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    rootPolynomial n ∣ telescoperNumerator n W := by
  unfold rootPolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact Polynomial.pairwise_coprime_X_sub_C (rootNode_injective n) hab
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact telescoperNumerator_zero_at_nodes n hn1 hn W hstrong hzero i

theorem actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], telescoperNumerator n W = rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3 := by
  obtain ⟨H, hH⟩ := all_kernel_nodes_divide_telescoperNumerator n hn1 hn W hstrong hzero
  refine ⟨H, hH, ?_⟩
  by_cases hH0 : H = 0
  · simp [hH0]
  · have hdegree := congrArg Polynomial.natDegree hH
    rw [Polynomial.natDegree_mul (rootPolynomial_monic n).ne_zero hH0, rootPolynomial_natDegree] at hdegree
    have hbound := telescoperNumerator_natDegree_le n hn1 W
    omega

end ZetaNine.CoefficientMapTelescoper

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapShiftDegree

open Polynomial

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

theorem actual_shift_difference_small_degree_implies_zero (n : ℕ) (hn : 1 ≤ n)
    (H : ℚ[X]) (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 := by
  by_contra hH
  have h := actual_shift_difference_degree_lower_bound n hn H hH hdeg
  omega

end ZetaNine.CoefficientMapShiftDegree




/-!
The genuine P0, R*A and shift identities linking the actual telescoper quotient
to a polynomial difference. No polynomial difference or trivial-kernel input is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapKernelBridge

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection
open CoefficientMapAggregate CoefficientMapTelescoper









theorem finite_product_shift_identity (n : ℕ) (f : ℕ → ℚ) :
    (∏ k ∈ range n, f (k + 1)) * f 0 = (∏ k ∈ range n, f k) * f n := by
  have h := Finset.prod_range_succ' f n
  rw [Finset.prod_range_succ] at h
  simpa only [mul_comm] using h.symm

theorem positiveProduct_shift (n : ℕ) (t : ℚ) :
    positiveProduct n (t + 1) * (t - (n : ℚ)) = t * positiveProduct n t := by
  have h := finite_product_shift_identity n (fun k => t - (k : ℚ))
  have he : positiveProduct n (t + 1) = ∏ k ∈ range n, (t - (k : ℚ)) := by
    unfold positiveProduct
    apply Finset.prod_congr rfl
    intro k hk
    ring
  rw [he]
  simpa only [positiveProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, mul_comm] using h.symm

theorem negativeProduct_shift (n : ℕ) (t : ℚ) :
    negativeProduct n (t + 1) * (t + (n : ℚ) + 1) =
      negativeProduct n t * (t + 2 * (n : ℚ) + 1) := by
  have h := finite_product_shift_identity n (fun k => t + (n : ℚ) + ((k : ℚ) + 1))
  have he : (∏ k ∈ range n, (t + (n : ℚ) + (((k + 1 : ℕ) : ℚ) + 1))) =
      negativeProduct n (t + 1) := by
    unfold negativeProduct
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he] at h
  have hend : t + (n : ℚ) + ((n : ℚ) + 1) = t + 2 * (n : ℚ) + 1 := by ring
  simpa only [negativeProduct, Nat.cast_zero, zero_add, hend] using h

theorem numerator_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
      CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1) := by
  change (n.factorial : ℚ) ^ 7 * positiveProduct n (t + 1) * negativeProduct n (t + 1) *
      (t - (n : ℚ)) * (t + (n : ℚ) + 1) =
    (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t * t * (t + 2 * (n : ℚ) + 1)
  calc
    _ = (n.factorial : ℚ) ^ 7 * (positiveProduct n (t + 1) * (t - (n : ℚ))) *
        (negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) := by ring
    _ = _ := by rw [positiveProduct_shift, negativeProduct_shift]; ring

theorem poleProduct_shift_identity (n : ℕ) (t : ℚ) :
    CoefficientMap.poleProduct n (t + 1) * t = CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
  have h := finite_product_shift_identity (n + 1) (fun k => t + (k : ℚ))
  simpa only [CoefficientMap.poleProduct, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
    add_assoc, add_comm, add_left_comm] using h

theorem actual_R_shift_A_equals_R_B (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0)
    (hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n (t + 1) * aValue n (t + 1) = CoefficientMap.actualR n t * bValue n t := by
  have hden := CoefficientMap.poleProduct_ne_zero n t hregular
  have hden1 := CoefficientMap.poleProduct_ne_zero n (t + 1) hregular1
  have hnum := numerator_shift_identity n t
  have hpole := congrArg (fun x : ℚ => x ^ 9) (poleProduct_shift_identity n t)
  simp only [mul_pow] at hpole
  unfold CoefficientMap.actualR aValue bValue
  field_simp [hden, hden1]
  calc
    _ = (CoefficientMap.numerator n (t + 1) * (t - (n : ℚ)) * (t + (n : ℚ) + 1)) *
        ((t + (n : ℚ) + 1) ^ 9 * CoefficientMap.poleProduct n t ^ 9) := by ring
    _ = (CoefficientMap.numerator n t * t * (t + 2 * (n : ℚ) + 1)) *
        (CoefficientMap.poleProduct n (t + 1) ^ 9 * t ^ 9) := by rw [hnum, hpole]; ring
    _ = _ := by ring

theorem rootPolynomial_numerator_factor (n : ℕ) (t : ℚ) :
    (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t =
      CoefficientMap.numerator n t * (t - (n : ℚ) - 1) * (t + (n : ℚ)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [Finset.prod_range_succ (fun k : ℕ => t - ((k : ℚ) + 1)) n,
    Finset.prod_range_succ' (fun k : ℕ => t + (n : ℚ) + (k : ℚ)) n]
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  change (n.factorial : ℚ) ^ 7 * ((positiveProduct n t * (t - ((n : ℚ) + 1))) *
      (negativeProduct n t * (t + (n : ℚ)))) = _
  change _ = (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t *
    (t - (n : ℚ) - 1) * (t + (n : ℚ))
  ring

theorem poleProduct_last_factor (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ) :
    CoefficientMap.poleProduct n t = (polePolynomial (n - 1)).eval t * (t + (n : ℚ)) := by
  rw [CoefficientMapPartialFractions.polePolynomial_eval]
  unfold CoefficientMap.poleProduct
  rw [show n - 1 + 1 = n by omega]
  exact Finset.prod_range_succ _ _

theorem actual_R_A_equals_Pzero (n : ℕ) (hn1 : 1 ≤ n) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR n t * aValue n t =
      (n.factorial : ℚ) ^ 7 * (rootPolynomial n).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  have hden := CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) t
    (by intro k hk; exact hregular k (by omega))
  have hlast := hregular n (by omega)
  rw [rootPolynomial_numerator_factor]
  unfold CoefficientMap.actualR aValue
  rw [poleProduct_last_factor n hn1, mul_pow]
  field_simp [hden, hlast]

theorem telescoper_quotient_as_R_A (n : ℕ) (hn1 : 1 ≤ n) (W H : ℚ[X])
    (hH : telescoperNumerator n W = rootPolynomial n * H) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = CoefficientMap.actualR n t * aValue n t * H.eval t / (n.factorial : ℚ) ^ 7 := by
  have hfactor : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  rw [telescoper_actual_rational_representation n hn1 W t
    (by intro k hk; exact hregular k (by omega)), hH, Polynomial.eval_mul,
    actual_R_A_equals_Pzero n hn1 t hregular]
  field_simp [hfactor]

theorem actual_R_ne_zero_above_n (n : ℕ) (t : ℚ) (ht : (n : ℚ) < t) : CoefficientMap.actualR n t ≠ 0 := by
  have ht0 : (0 : ℚ) < t := lt_of_le_of_lt (Nat.cast_nonneg n) ht
  apply div_ne_zero
  · unfold CoefficientMap.numerator
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
      · apply Finset.prod_ne_zero_iff.mpr
        intro k hk
        have hk1 : (k : ℚ) + 1 ≤ (n : ℚ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        exact ne_of_gt (by linarith)
    · apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      exact ne_of_gt (by positivity)
  · exact pow_ne_zero _ (CoefficientMap.poleProduct_ne_zero n t
      (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))))

theorem kernel_actual_polynomial_relation (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W H : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hH : telescoperNumerator n W = rootPolynomial n * H) :
    C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) =
      ((X - C ((n : ℚ) + 1)) * (X + C (n : ℚ)) ^ 10) * H -
        (X ^ 10 * (X + C (2 * (n : ℚ) + 1))) * H.comp (X + C 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite ((n : ℚ) + 1)).mono
  intro t ht
  have ht1 : (n : ℚ) + 1 < t := ht
  have ht0 : (0 : ℚ) < t := by have hnonneg : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n; linarith
  have hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg ht0 (Nat.cast_nonneg k))
  have hregular1 : ∀ k ≤ n, (t + 1) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hR : CoefficientMap.actualR n t ≠ 0 := actual_R_ne_zero_above_n n t (by linarith)
  have hfac : (n.factorial : ℚ) ^ 7 ≠ 0 := pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero)
  have hdiff := actual_weightedR_is_difference n hn W hstrong hzero t hregular
  rw [telescoper_quotient_as_R_A n hn1 W H hH t hregular,
    telescoper_quotient_as_R_A n hn1 W H hH (t + 1) hregular1] at hdiff
  rw [actual_R_shift_A_equals_R_B n t hregular hregular1] at hdiff
  unfold CoefficientMap.weightedR at hdiff
  have he : (n.factorial : ℚ) ^ 7 * W.eval (t * (t + (n : ℚ))) =
      aValue n t * H.eval t - bValue n t * H.eval (t + 1) := by
    field_simp [hfac] at hdiff
    nlinarith [hdiff]
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    baseU, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    aValue, bValue, sub_sub, add_assoc] using he

theorem checked_original_quartic_aggregate_kernel_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) : W = 0 := by
  have hstrong := quartic_is_strong_proper n (by omega) W hW
  obtain ⟨H, hH, hdegree⟩ := actual_polynomial_quotient_degree_bound n (by omega) hn W hstrong hzero
  have hrelation := kernel_actual_polynomial_relation n (by omega) hn W H hstrong hzero hH
  have hdiff : CoefficientMapShiftDegree.shiftDifference n H =
      C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n) := hrelation.symm
  have hsmall : (CoefficientMapShiftDegree.shiftDifference n H).natDegree ≤ 8 := by
    rw [hdiff]
    have hmul : (C ((n.factorial : ℚ) ^ 7) * W.comp (baseU n)).natDegree ≤
        (C ((n.factorial : ℚ) ^ 7)).natDegree + (W.comp (baseU n)).natDegree := Polynomial.natDegree_mul_le
    have hcomp := Polynomial.natDegree_comp_le (p := W) (q := baseU n)
    rw [Polynomial.natDegree_C, zero_add] at hmul
    rw [baseU_natDegree] at hcomp
    omega
  have hH0 := CoefficientMapShiftDegree.actual_shift_difference_small_degree_implies_zero n (by omega) H hdegree hsmall
  rw [hH0] at hdiff
  simp only [CoefficientMapShiftDegree.shiftDifference, Polynomial.zero_comp, mul_zero, sub_zero] at hdiff
  have hcomp : W.comp (baseU n) = 0 := by
    have hfac : C ((n.factorial : ℚ) ^ 7) ≠ (0 : ℚ[X]) :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast n.factorial_ne_zero))
    exact (mul_eq_zero.mp hdiff.symm).resolve_left hfac
  apply weightedNumerator_zero_implies_multiplier_zero n W
  simp only [weightedNumerator, hcomp, mul_zero]

theorem original_quartic_aggregate_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℚ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : aggregate n W = aggregate n V) : W = V := by
  have hdegree : (W - V).natDegree ≤ 4 :=
    le_trans (Polynomial.natDegree_sub_le W V) (max_le hW hV)
  have hzero : aggregate n (W - V) = 0 := by
    change aggregateLinearMap n (W - V) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr heq
  exact sub_eq_zero.mp (checked_original_quartic_aggregate_kernel_zero n hn2 hn (W - V) hdegree hzero)

theorem original_five_dimensional_map_injective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Injective (quarticAggregateLinearMap n) := by
  intro a b heq
  apply coordinatePolynomial_injective
  exact original_quartic_aggregate_injective n hn2 hn (coordinatePolynomial a) (coordinatePolynomial b)
    (coordinatePolynomial_natDegree_le a) (coordinatePolynomial_natDegree_le b) heq

theorem original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (quarticAggregateLinearMap n) := by
  have hi := original_five_dimensional_map_injective n hn2 hn
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩



theorem every_exact_formal_output_has_unique_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) : ∃! W : {W : ℚ[X] // W.natDegree ≤ 4}, aggregate n W.val = b := by
  obtain ⟨a, ha⟩ := (original_five_dimensional_map_bijective n hn2 hn).surjective b
  refine ⟨⟨coordinatePolynomial a, coordinatePolynomial_natDegree_le a⟩, ha, ?_⟩
  intro V hV
  apply Subtype.ext
  exact original_quartic_aggregate_injective n hn2 hn V.val (coordinatePolynomial a) V.property
    (coordinatePolynomial_natDegree_le a) (hV.trans ha.symm)





theorem inverseMultiplier_natDegree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := coordinatePolynomial_natDegree_le _

theorem inverseMultiplier_actual_aggregate (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    aggregate n (inverseMultiplier n hn2 hn b) = b := by
  change (actualAggregateEquiv n hn2 hn) ((actualAggregateEquiv n hn2 hn).symm b) = b
  exact (actualAggregateEquiv n hn2 hn).apply_symm_apply b

theorem inverseMultiplier_unique (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hWb : aggregate n W = b) : W = inverseMultiplier n hn2 hn b :=
  original_quartic_aggregate_injective n hn2 hn W _ hW (inverseMultiplier_natDegree_le n hn2 hn b)
    (hWb.trans (inverseMultiplier_actual_aggregate n hn2 hn b).symm)

theorem inverseMultiplier_nonzero_of_output_nonzero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) (hb : b ≠ 0) : inverseMultiplier n hn2 hn b ≠ 0 := by
  intro hW0
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  rw [hW0] at h
  have hF0 : aggregate n (0 : ℚ[X]) = 0 := (aggregateLinearMap n).map_zero
  exact hb (h.symm.trans hF0)

theorem inverseMultiplier_exact_L (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    CoefficientMapSummation.exactL n (inverseMultiplier n hn2 hn b) = prescribedL b := by
  have h := inverseMultiplier_actual_aggregate n hn2 hn b
  have hB : CoefficientMapFiniteSum.constantTerm n (inverseMultiplier n hn2 hn b) = b 0 := congrFun h 0
  have h3 : CoefficientMapFiniteSum.rho n 3 (inverseMultiplier n hn2 hn b) = b 1 := congrFun h 1
  have h5 : CoefficientMapFiniteSum.rho n 5 (inverseMultiplier n hn2 hn b) = b 2 := congrFun h 2
  have h7 : CoefficientMapFiniteSum.rho n 7 (inverseMultiplier n hn2 hn b) = b 3 := congrFun h 3
  have h9 : CoefficientMapFiniteSum.rho n 9 (inverseMultiplier n hn2 hn b) = b 4 := congrFun h 4
  simp only [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9, prescribedL]

theorem inverseMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)) (prescribedL b) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  have hstrong := quartic_is_strong_proper n (by omega) _ (inverseMultiplier_natDegree_le n hn2 hn b)
  constructor
  · have h := CoefficientMapSummation.actualSeries_hasSum_exactL n hn _ hstrong
    rw [inverseMultiplier_exact_L n hn2 hn b] at h
    exact h
  · exact CoefficientMapSummation.actualSeries_norm_summable n _ hstrong

end ZetaNine.CoefficientMapKernelBridge




















open ZetaNine ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapAggregate ZetaNine.HarmonicStability

theorem solution (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) : W = 0 := by
  exact ZetaNine.CoefficientMapKernelBridge.checked_original_quartic_aggregate_kernel_zero n hn2 hn W hW hzero

#print axioms solution
