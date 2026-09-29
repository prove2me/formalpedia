-- Prove2me | solution 1 for WeightedHilbert_cauchy_translation_average_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T16:11:52.557283+00:00
-- url     : https://prove2.me/submissions/eb99ccab-16ba-4f65-b67b-6e02c31a5341

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Filter
noncomputable section
namespace WeightedHilbert

/-- Exact triangular multiplicities for a finite translation block. No estimate
or convergence is assumed in this discrete identity. -/
theorem sum_translation_block {A : Type*} [AddCommMonoid A] (f : ℤ → A) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f ((i : ℤ) - j)) =
      ∑ m ∈ Finset.range n,
        (f 0 + ∑ k ∈ Finset.range m, (f (-((k : ℤ) + 1)) + f ((k : ℤ) + 1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hneg : (∑ i ∈ Finset.range n, f ((i : ℤ) - n)) =
        ∑ k ∈ Finset.range n, f (-((k : ℤ) + 1)) := by
      rw [← Finset.sum_range_reflect (fun i => f ((i : ℤ) - n)) n]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      congr 1
      omega
    have hpos : (∑ j ∈ Finset.range n, f ((n : ℤ) - j)) =
        ∑ k ∈ Finset.range n, f ((k : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect (fun j => f ((n : ℤ) - j)) n]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      congr 1
      omega
    calc
      _ = ((∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f ((i : ℤ) - j)) +
          (∑ i ∈ Finset.range n, f ((i : ℤ) - n))) +
          ((∑ j ∈ Finset.range n, f ((n : ℤ) - j)) + f 0) := by
        simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
        ac_rfl
      _ = ((∑ m ∈ Finset.range n,
          (f 0 + ∑ k ∈ Finset.range m, (f (-((k : ℤ) + 1)) + f ((k : ℤ) + 1)))) +
          (∑ k ∈ Finset.range n, f (-((k : ℤ) + 1)))) +
          ((∑ k ∈ Finset.range n, f ((k : ℤ) + 1)) + f 0) := by rw [ih, hneg, hpos]
      _ = _ := by
        simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
        ac_rfl

/-- Cesaro compression of the real Cauchy kernel converges to the cotangent
kernel. This is the analytic interface for transferring a finite real-frequency
Hilbert estimate to phases modulo one. -/
theorem cauchy_translation_average_tendsto (x : ℂ) (hx : x ∈ Complex.integerComplement) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) •
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (x + (i : ℂ) - (j : ℂ))⁻¹))
      atTop (𝓝 ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))) := by
  have hpartial : Tendsto (fun n : ℕ => x⁻¹ + ∑ k ∈ Finset.range n, cotTerm x k)
      atTop (𝓝 ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))) := by
    have h := (tendsto_const_nhds (x := x⁻¹)).add
      (tendsto_logDeriv_euler_cot_sub hx)
    have he : x⁻¹ + ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) - 1 / x) =
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x) := by
      simp only [one_div]
      ring
    rw [he] at h
    exact h
  have hid (n : ℕ) :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (x + (i : ℂ) - (j : ℂ))⁻¹) =
        ∑ m ∈ Finset.range n, (x⁻¹ + ∑ k ∈ Finset.range m, cotTerm x k) := by
    simpa only [cotTerm, one_div, Int.cast_sub, Int.cast_natCast, Int.cast_neg,
      Int.cast_add, Int.cast_one, Int.cast_zero, add_zero, sub_eq_add_neg, add_assoc]
      using sum_translation_block (fun k : ℤ => (x + (k : ℂ))⁻¹) n
  simpa only [hid] using hpartial.cesaro_smul

end WeightedHilbert
#print axioms WeightedHilbert.sum_translation_block
#print axioms WeightedHilbert.cauchy_translation_average_tendsto

theorem solution (x : ℂ) (hx : x ∈ Complex.integerComplement) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) •
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (x + (i : ℂ) - (j : ℂ))⁻¹))
      atTop (𝓝 ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))) :=
  WeightedHilbert.cauchy_translation_average_tendsto x hx

#print axioms solution
