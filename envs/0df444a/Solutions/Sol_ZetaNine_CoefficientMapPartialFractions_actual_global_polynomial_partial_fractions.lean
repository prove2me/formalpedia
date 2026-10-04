-- Prove2me | solution 1 for ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T18:19:37.327928+00:00
-- url     : https://prove2.me/submissions/53eb2686-f65a-41b0-ad69-f08c7c741cbf

import Definitions.Def_ZetaNine_CoefficientMapPartialFractions
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Trunc

open scoped BigOperators
open Finset Polynomial

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




/-!
Global partial fractions for the actual finite p=9, q=1, m=n rational
function, with coefficients from the frozen actual local formal series.
This does not assert vanishing of the simple-pole total, an infinite-sum
identity, or invertibility of the original five aggregated outputs.
-/

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

theorem actual_series_from_shifted_numerator (n j : ℕ) (W : ℚ[X]) :
    CoefficientMapJet.weightedClearedSeries n j W =
      ((weightedNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
        ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := by
  rw [weightedNumerator_shift]
  simp only [CoefficientMapJet.weightedClearedSeries, CoefficientMapJet.clearedSeries,
    Polynomial.coe_mul]
  ring

theorem candidateClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
    candidateClearedSeries n j W *
        (CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      ((partialNumerator n W).comp (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff
      ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero n j)
  unfold candidateClearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

-- This uses the local truncation/divisibility result, without global PF or properness.
theorem candidate_first_nine_coefficients (n j : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (k : ℕ) (hk : k < 9) :
    PowerSeries.coeff k (candidateClearedSeries n j W) =
      PowerSeries.coeff k (CoefficientMapJet.weightedClearedSeries n j W) := by
  obtain ⟨q, hq⟩ := full_candidate_matches_nine_jets n j W hj
  have hs : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣
      ((weightedNumerator n W - partialNumerator n W).comp
        (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) := by
    refine ⟨(q : PowerSeries ℚ), ?_⟩
    have he := congrArg (fun p : ℚ[X] => (p : PowerSeries ℚ)) hq
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X] using he
  have hm := dvd_mul_of_dvd_left hs
    (((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹)
  have he : (((weightedNumerator n W - partialNumerator n W).comp
      (CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) *
        ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) =
      CoefficientMapJet.weightedClearedSeries n j W - candidateClearedSeries n j W := by
    rw [Polynomial.sub_comp, Polynomial.coe_sub, sub_mul, ← actual_series_from_shifted_numerator]
    rfl
  rw [he] at hm
  have hz := PowerSeries.X_pow_dvd_iff.mp hm k hk
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem candidate_local_coefficients (n j s : ℕ) (W : ℚ[X]) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    PowerSeries.coeff (9 - s) (candidateClearedSeries n j W) =
      CoefficientMapJet.weightedLocalCoefficient n j s W := by
  exact candidate_first_nine_coefficients n j W hj (9 - s) (by omega)

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

theorem checked_actual_global_polynomial_partial_fractions (n : ℕ) (W : ℚ[X])
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
  rw [actual_weighted_rational_representation, checked_actual_global_polynomial_partial_fractions n W hproper]
  simp only [partialNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  exact partial_term_division n j s W t (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2 hregular

end ZetaNine.CoefficientMapPartialFractions















open ZetaNine ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapInjectivity

theorem solution (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) : weightedNumerator n W = partialNumerator n W := by
  exact ZetaNine.CoefficientMapPartialFractions.checked_actual_global_polynomial_partial_fractions n W hproper

#print axioms solution
