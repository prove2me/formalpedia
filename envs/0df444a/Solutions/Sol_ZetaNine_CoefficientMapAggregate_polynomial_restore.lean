-- Prove2me | solution 1 for ZetaNine.CoefficientMapAggregate.polynomial_restore
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T22:30:03.982384+00:00
-- url     : https://prove2.me/submissions/2ca2ab5c-5cbe-428f-bbf9-de1c5b5fde76

import Definitions.Def_ZetaNine_CoefficientMapAggregate
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.BigOperators

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




/-!
The genuine five-dimensional formal map, separate from the full local array.
Its entries use the actual finite harmonic constant and actual local series.
No determinant, rank, kernel triviality or inverse-map conclusion is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapAggregate

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

theorem coordinatePolynomial_coeff_above (a : Fin 5 → ℚ) (k : ℕ) (hk : 5 ≤ k) :
    (coordinatePolynomial a).coeff k = 0 := by
  classical
  simp only [coordinatePolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro i hi
  have h : k ≠ i.val := by have := i.isLt; omega
  simp [h]

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

theorem checked_polynomial_restore (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    coordinatePolynomial (polynomialCoordinates W) = W := by
  ext k
  by_cases hk : k < 5
  · exact coordinatePolynomial_coeff (polynomialCoordinates W) ⟨k, hk⟩
  · rw [coordinatePolynomial_coeff_above _ k (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

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









open ZetaNine ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation ZetaNine.HarmonicStability

theorem solution (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    coordinatePolynomial (polynomialCoordinates W) = W := by
  exact ZetaNine.CoefficientMapAggregate.checked_polynomial_restore W hW

#print axioms solution
