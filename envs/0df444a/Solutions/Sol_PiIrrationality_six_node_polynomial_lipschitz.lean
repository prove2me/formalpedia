-- Prove2me | solution 1 for PiIrrationality.six_node_polynomial_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T17:01:16.929074+00:00
-- url     : https://prove2.me/submissions/ca6dd689-ba3b-40c7-92b3-38eb0f792f94

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
open Polynomial Finset

lemma polynomial_lipschitz_on_two (p : ℂ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℂ, ‖a‖ ≤ 2 → ‖b‖ ≤ 2 →
      ‖p.eval a - p.eval b‖ ≤ C * ‖a-b‖ := by
  have hc : Continuous (fun z : ℂ => ‖p.derivative.eval z‖) := p.derivative.continuous.norm
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_isMaxOn
    ⟨0, by simp⟩ hc.continuousOn
  refine ⟨‖p.derivative.eval z‖, norm_nonneg _, fun a b ha hb => ?_⟩
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => p.differentiableAt)
    (fun x hx => ?_) (convex_closedBall (0 : ℂ) 2)
    (show b ∈ Metric.closedBall (0 : ℂ) 2 by simpa using hb)
    (show a ∈ Metric.closedBall (0 : ℂ) 2 by simpa using ha)
  rw [p.deriv]
  exact hmax hx

theorem solution (v : Fin 6 → ℂ) (hv : Function.Injective v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : ℂ[X]) (B : ℝ),
      p.degree < 6 → 0 ≤ B → (∀ i, ‖p.eval (v i)‖ ≤ B) →
      ∀ a b : ℂ, ‖a‖ ≤ 2 → ‖b‖ ≤ 2 →
        ‖p.eval a - p.eval b‖ ≤ C * B * ‖a-b‖ := by
  classical
  let L := fun i : Fin 6 => Lagrange.basis Finset.univ v i
  choose K hK using (fun i : Fin 6 => polynomial_lipschitz_on_two (L i))
  have hsum : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => (hK i).1)
  refine ⟨1 + ∑ i, K i, by linarith, fun p B hp hB hvalues a b ha hb => ?_⟩
  have heq := Lagrange.eq_interpolate (s := Finset.univ) (v := v)
    (fun i _ j _ hij => hv hij) (f := p) (by simpa using hp)
  have hevala : p.eval a = ∑ i, p.eval (v i) * (L i).eval a := by
    have := congrArg (fun f : ℂ[X] => f.eval a) heq
    simpa [Lagrange.interpolate_apply, L, Polynomial.eval_finsetSum] using this
  have hevalb : p.eval b = ∑ i, p.eval (v i) * (L i).eval b := by
    have := congrArg (fun f : ℂ[X] => f.eval b) heq
    simpa [Lagrange.interpolate_apply, L, Polynomial.eval_finsetSum] using this
  have hdiff : p.eval a - p.eval b = ∑ i, p.eval (v i) * ((L i).eval a - (L i).eval b) := by
    rw [hevala, hevalb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdiff]
  calc
    _ ≤ ∑ i, ‖p.eval (v i) * ((L i).eval a - (L i).eval b)‖ := norm_sum_le _ _
    _ ≤ ∑ i, B * (K i * ‖a-b‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (hvalues i) ((hK i).2 a b ha hb) (norm_nonneg _) hB
    _ = (∑ i, K i) * B * ‖a-b‖ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    _ ≤ (1 + ∑ i, K i) * B * ‖a-b‖ := by nlinarith [mul_nonneg hB (norm_nonneg (a-b))]

