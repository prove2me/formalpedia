-- Prove2me | solution 1 for ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T17:17:05.0895+00:00
-- url     : https://prove2.me/submissions/16e2a001-e3b1-4c49-a2bb-3edaaee967fb

import Definitions.Def_ZetaNine_CoefficientMapInjectivity
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

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




/-!
Injectivity of the complete (n+1) by 9 actual local coefficient array in
the strict proper-degree domain. This is a bridge for route Z9.F, not
injectivity/invertibility of its five aggregated zeta/constant outputs.
The genuine numerator and the frozen formal jets are used throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
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

theorem zero_local_jet_implies_shifted_numerator_divisibility (n j : ℕ) (W : ℚ[X])
    (hzero : ∀ s, 1 ≤ s → s ≤ 9 → CoefficientMapJet.weightedLocalCoefficient n j s W = 0) :
    (X : ℚ[X]) ^ 9 ∣ CoefficientMapJet.shiftedNumerator n j *
      W.comp (CoefficientMapJet.localU n j) := by
  have hseries : (PowerSeries.X : PowerSeries ℚ) ^ 9 ∣
      CoefficientMapJet.weightedClearedSeries n j W := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    have h := hzero (9 - k) (by omega) (by omega)
    have hindex : 9 - (9 - k) = k := by omega
    simpa only [CoefficientMapJet.weightedLocalCoefficient, hindex] using h
  have hproduct := dvd_mul_of_dvd_left hseries
    ((CoefficientMapJet.shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)
  rw [CoefficientMapJet.weightedClearedSeries_denominator_identity] at hproduct
  apply Polynomial.X_pow_dvd_iff.mpr
  intro k hk
  have h := PowerSeries.X_pow_dvd_iff.mp hproduct k hk
  simpa only [Polynomial.coeff_coe] using h

theorem zero_local_jet_implies_pole_divisibility (n j : ℕ) (W : ℚ[X])
    (hzero : ∀ s, 1 ≤ s → s ≤ 9 → CoefficientMapJet.weightedLocalCoefficient n j s W = 0) :
    (X + C (j : ℚ)) ^ 9 ∣ weightedNumerator n W := by
  have h := zero_local_jet_implies_shifted_numerator_divisibility n j W hzero
  rw [← weightedNumerator_shift n j W] at h
  obtain ⟨q, hq⟩ := h
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  have he := congrArg (fun p : ℚ[X] => p.comp (X + C (j : ℚ))) hq
  simpa only [Polynomial.comp_assoc, CoefficientMapJet.shiftedVariable,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel_right,
    Polynomial.comp_X, Polynomial.mul_comp, Polynomial.pow_comp] using he

theorem pole_factors_coprime (a b : ℕ) (hab : a ≠ b) :
    IsCoprime ((X + C (a : ℚ)) ^ 9) ((X + C (b : ℚ)) ^ 9) := by
  have hneq : (-(a : ℚ)) ≠ -(b : ℚ) := by
    intro h
    exact hab (Nat.cast_inj.mp (neg_inj.mp h))
  have hc := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    (sub_ne_zero_of_ne hneq).isUnit
  have hp := hc.pow (m := 9) (n := 9)
  simpa only [map_neg, sub_neg_eq_add] using hp

theorem all_zero_jets_imply_full_denominator_divisibility (n : ℕ) (W : ℚ[X])
    (hzero : AllLocalCoefficientsZero n W) : polePolynomial n ^ 9 ∣ weightedNumerator n W := by
  unfold polePolynomial
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact pole_factors_coprime a b hab
  · intro j hj
    exact zero_local_jet_implies_pole_divisibility n j W
      (hzero j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

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

theorem checked_all_local_coefficients_zero_implies_zero (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hzero : AllLocalCoefficientsZero n W) : W = 0 := by
  have hdvd := all_zero_jets_imply_full_denominator_divisibility n W hzero
  have hnumzero : weightedNumerator n W = 0 := by
    by_contra hnum
    have hdeg := Polynomial.natDegree_le_of_dvd hdvd hnum
    rw [polePolynomial_pow_natDegree] at hdeg
    have hbound := weightedNumerator_natDegree_le n W
    unfold ProperMultiplier at hproper
    omega
  exact weightedNumerator_zero_implies_multiplier_zero n W hnumzero

theorem weightedLocalCoefficient_sub (n j s : ℕ) (W V : ℚ[X]) :
    CoefficientMapJet.weightedLocalCoefficient n j s (W - V) =
      CoefficientMapJet.weightedLocalCoefficient n j s W -
        CoefficientMapJet.weightedLocalCoefficient n j s V := by
  simp only [CoefficientMapJet.weightedLocalCoefficient, CoefficientMapJet.weightedClearedSeries,
    Polynomial.sub_comp, Polynomial.coe_sub, mul_sub, map_sub]

theorem local_coefficients_injective (n : ℕ) (W V : ℚ[X])
    (hW : ProperMultiplier n W) (hV : ProperMultiplier n V)
    (heq : ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
      CoefficientMapJet.weightedLocalCoefficient n j s W =
        CoefficientMapJet.weightedLocalCoefficient n j s V) : W = V := by
  have hdiff : ProperMultiplier n (W - V) := by
    have hdeg := Polynomial.natDegree_sub_le W V
    unfold ProperMultiplier at *
    rcases le_total W.natDegree V.natDegree with h | h
    · rw [max_eq_right h] at hdeg
      omega
    · rw [max_eq_left h] at hdeg
      omega
  have hzero : AllLocalCoefficientsZero n (W - V) := by
    intro j hj s hs1 hs9
    rw [weightedLocalCoefficient_sub, heq j hj s hs1 hs9, sub_self]
  exact sub_eq_zero.mp (checked_all_local_coefficients_zero_implies_zero n (W - V) hdiff hzero)

theorem fullLocalCoefficientMap_injective (n : ℕ) :
    Function.Injective (fun W : {W : ℚ[X] // ProperMultiplier n W} => fullLocalCoefficientMap n W.val) := by
  intro W V heq
  apply Subtype.ext
  apply local_coefficients_injective n W.val V.val W.property V.property
  intro j hj s hs1 hs9
  have hfin : s - 1 < 9 := by omega
  have hindex : s - 1 + 1 = s := by omega
  have h := congrFun (congrFun heq ⟨j, Nat.lt_succ_of_le hj⟩) ⟨s - 1, hfin⟩
  simpa only [fullLocalCoefficientMap, hindex] using h

theorem quartic_is_proper (n : ℕ) (W : ℚ[X]) (hW : W.natDegree ≤ 4) : ProperMultiplier n W := by
  unfold ProperMultiplier
  omega

end ZetaNine.CoefficientMapInjectivity












open ZetaNine.CoefficientMapInjectivity

theorem solution (n : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hzero : AllLocalCoefficientsZero n W) : W = 0 := by
  exact ZetaNine.CoefficientMapInjectivity.checked_all_local_coefficients_zero_implies_zero n W hproper hzero

#print axioms solution
