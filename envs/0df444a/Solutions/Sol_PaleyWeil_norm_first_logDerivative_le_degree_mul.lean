-- Prove2me | solution 1 for PaleyWeil.norm_first_logDerivative_le_degree_mul
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:43:05.663403+00:00
-- url     : https://prove2.me/submissions/1a07f4d3-cf9f-473c-bfcc-b02e065f8604

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_ComplexRootAmplification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace
import Theorems.Thm_Complex_norm_le_of_forall_norm_sum_pow_le
import Theorems.Thm_PaleyWeil_exists_normalized_linear_factors

namespace Finset
end Finset
namespace PaleyWeil
end PaleyWeil
namespace Polynomial
end Polynomial

section


/-!
A finite polynomial with constant coefficient one has an exact logarithmic
derivative given by the power sums of its reciprocal roots. A uniform
exponential bound on those power sums bounds each reciprocal root. This is
the sharpness amplification step; it uses no character-sum assumption.
-/

open Polynomial Finset
open scoped PowerSeries

namespace PaleyWeil

noncomputable section







@[simp] theorem coeff_complexPositivePowers (w : ℂ) (n : ℕ) :
    PowerSeries.coeff n (complexPositivePowers w) =
      if n = 0 then 0 else w ^ n := by
  simp only [complexPositivePowers, map_sub, PowerSeries.coeff_rescale,
    PowerSeries.coeff_mk, Pi.one_apply, mul_one, PowerSeries.coeff_one]
  split_ifs with h <;> simp [h]

theorem complexPositivePowers_mul (w : ℂ) :
    complexPositivePowers w * (1 - PowerSeries.C w * PowerSeries.X) =
      PowerSeries.C w * PowerSeries.X := by
  have h := congrArg (PowerSeries.rescale w)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h
  dsimp only [complexPositivePowers]
  linear_combination h

theorem complex_linear_logDerivative (w : ℂ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ)
        (1 - PowerSeries.C w * PowerSeries.X) =
      -(complexPositivePowers w) * (1 - PowerSeries.C w * PowerSeries.X) := by
  rw [neg_mul, complexPositivePowers_mul]
  simp only [map_sub, PowerSeries.derivative_one, Derivation.leibniz,
    smul_eq_mul, PowerSeries.derivative_C, PowerSeries.derivative_X,
    mul_one, mul_zero, add_zero, zero_sub]
  ring





@[simp] theorem coeff_complexPowerSums (l : List ℂ) (n : ℕ) :
    PowerSeries.coeff n (complexPowerSums l) =
      if n = 0 then 0 else (l.map fun w ↦ w ^ n).sum := by
  induction l with
  | nil => simp [complexPowerSums]
  | cons w l ih =>
    simp only [complexPowerSums, List.map_cons, List.sum_cons, map_add] at *
    rw [ih, coeff_complexPositivePowers]
    split_ifs <;> simp

theorem complex_factor_logDerivative (l : List ℂ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (complexFactorProduct l) =
      -(complexPowerSums l) * complexFactorProduct l := by
  induction l with
  | nil => simp [complexFactorProduct, complexPowerSums]
  | cons w l ih =>
    have hw := complex_linear_logDerivative w
    simp only [complexFactorProduct, complexPowerSums, List.map_cons,
      List.prod_cons, List.sum_cons] at *
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    linear_combination
      (1 - PowerSeries.C w * PowerSeries.X) * ih +
        (l.map fun w ↦ (1 - PowerSeries.C w * PowerSeries.X : ℂ⟦X⟧)).prod * hw

theorem coe_complex_factor_product (l : List ℂ) :
    (((l.map fun w ↦ (1 - C w * X : ℂ[X])).prod : ℂ[X]) : ℂ⟦X⟧) =
      complexFactorProduct l := by
  induction l with
  | nil => simp [complexFactorProduct]
  | cons w l ih =>
    simp only [List.map_cons, List.prod_cons, Polynomial.coe_mul,
      Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X,
      ih, complexFactorProduct]






end
end PaleyWeil

end

/-!
A finite polynomial with constant coefficient one has an exact logarithmic
derivative given by the power sums of its reciprocal roots. A uniform
exponential bound on those power sums bounds each reciprocal root. This is
the sharpness amplification step; it uses no character-sum assumption.
-/
open Polynomial Finset
open scoped PowerSeries
open PaleyWeil

theorem solution
    (P : ℂ[X]) (h0 : P.coeff 0 = 1) (B : ℕ → ℂ)
    (hD : PowerSeries.X * PowerSeries.derivative (R := ℂ) (P : ℂ⟦X⟧) =
      PowerSeries.mk B * (P : ℂ⟦X⟧))
    {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ n : ℕ, 0 < n → ‖B n‖ ≤ C * R ^ n) :
    ‖B 1‖ ≤ (P.natDegree : ℝ) * R := by
  obtain ⟨l, hlcard, hlfac⟩ := exists_normalized_linear_factors P h0
  have hP : (P : ℂ⟦X⟧) ≠ 0 := by
    intro h
    have hz := congrArg PowerSeries.constantCoeff h
    apply one_ne_zero (α := ℂ)
    simpa only [Polynomial.constantCoeff_coe, h0, PowerSeries.constantCoeff_zero] using hz
  have hfactor : (P : ℂ⟦X⟧) = complexFactorProduct l := by
    rw [hlfac, coe_complex_factor_product]
  have heq : PowerSeries.mk B = -complexPowerSums l := by
    apply mul_right_cancel₀ hP
    rw [← hD, hfactor, complex_factor_logDerivative]
  have hBn (n : ℕ) (hn : 0 < n) : B n = -(l.map fun w ↦ w ^ n).sum := by
    have h := congrArg (PowerSeries.coeff n) heq
    simpa only [PowerSeries.coeff_mk, map_neg, coeff_complexPowerSums,
      if_neg hn.ne'] using h
  have hsum (n : ℕ) : (∑ i : Fin l.length, l.get i ^ n) =
      (l.map fun w ↦ w ^ n).sum := by
    have h := congrArg List.sum (List.ofFn_comp' l.get (fun w : ℂ ↦ w ^ n))
    rw [List.ofFn_get, List.sum_ofFn] at h
    exact h
  have hroots (i : Fin l.length) : ‖l.get i‖ ≤ R := by
    apply Complex.norm_le_of_forall_norm_sum_pow_le (ω := l.get) (C := C) hR
      (fun n hn ↦ ?_) i
    rw [hsum, ← norm_neg, ← hBn n hn]
    exact hbound n hn
  calc
    ‖B 1‖ = ‖∑ i : Fin l.length, l.get i‖ := by
      rw [hBn 1 (by decide), norm_neg, ← hsum]
      simp only [pow_one]
    _ ≤ ∑ i : Fin l.length, ‖l.get i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin l.length, R := Finset.sum_le_sum (fun i _ ↦ hroots i)
    _ = (l.length : ℝ) * R := by simp
    _ ≤ (P.natDegree : ℝ) * R :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlcard) hR.le
