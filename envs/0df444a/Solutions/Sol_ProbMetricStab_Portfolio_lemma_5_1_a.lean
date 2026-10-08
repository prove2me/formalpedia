-- Prove2me | solution 1 for ProbMetricStab.Portfolio.lemma_5_1_a
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:07:46.368342+00:00
-- url     : https://prove2.me/submissions/ad7f8613-1595-47a4-bedf-1eb7057a773d

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio

private lemma norm_simplex {s : ℕ} {x : Rs s} (hx : x ∈ simplex s) : ‖x‖ ≤ 1 := by
  have hi (i : Fin s) : x i ≤ 1 := by
    rw [← hx.2]
    exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  have hs : ‖x‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← hx.2]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hx.1 i, hi i]
  nlinarith [norm_nonneg x]

private lemma power_lip (α : ℝ) (hα : 1 ≤ α) {a b : ℝ}
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    |a ^ α - b ^ α| ≤ α * |a - b| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z : ℝ => z ^ α) (C := α)
    (fun z _ => (Real.differentiable_rpow_const hα) z)
    (fun z hz => ?_) (convex_Icc 0 1) hb ha
  · simpa only [Real.norm_eq_abs] using hh
  · rw [Real.deriv_rpow_const, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hz.1 _))]
    calc
      α * z ^ (α - 1) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_one hz.1 hz.2 (by linarith)) (by linarith)
      _ = α := mul_one α

private lemma inner_bound {s : ℕ} {x ξ : Rs s} (hx : x ∈ simplex s)
    (hξ : ξ ∈ unitSphere s) : |inner ℝ x ξ| ≤ 1 := by
  have hn : ‖ξ‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hξ
  calc
    _ ≤ ‖x‖ * ‖ξ‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 := by rw [hn, mul_one]; exact norm_simplex hx

end ProbMetricStab.Portfolio

open ProbMetricStab.Portfolio

theorem solution {s : ℕ} (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) :
    (∀ ξ ∈ unitSphere s, ConvexOn ℝ Set.univ (fun x : Rs s => f0 α ξ x)) ∧
    (∀ x ∈ simplex s, ∀ x' ∈ simplex s, ∀ ξ ∈ unitSphere s, ∀ ξ' ∈ unitSphere s,
      |f0 α ξ x - f0 α ξ' x'| ≤ α * (‖ξ - ξ'‖ + ‖x - x'‖)) := by
  constructor
  · intro ξ hξ
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    dsimp [f0]
    have hlin : (inner ℝ (a • x + b • y) ξ : ℝ) =
        a * inner ℝ x ξ + b * inner ℝ y ξ := by
      simp [inner_add_left, inner_smul_left]
    rw [hlin]
    calc
      |a * inner ℝ x ξ + b * inner ℝ y ξ| ^ α
          ≤ (a * |inner ℝ x ξ| + b * |inner ℝ y ξ|) ^ α := by
        apply Real.rpow_le_rpow (abs_nonneg _) _ (by linarith)
        calc
          _ ≤ |a * inner ℝ x ξ| + |b * inner ℝ y ξ| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a • |inner ℝ x ξ| ^ α + b • |inner ℝ y ξ| ^ α :=
        (convexOn_rpow hα1.le).2
          (by change 0 ≤ |inner ℝ x ξ|; exact abs_nonneg _)
          (by change 0 ≤ |inner ℝ y ξ|; exact abs_nonneg _) ha hb hab
  · intro x hx x' hx' ξ hξ ξ' hξ'
    have hn : ‖ξ‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hξ
    have hb : |inner ℝ x ξ - inner ℝ x' ξ'| ≤ ‖ξ - ξ'‖ + ‖x - x'‖ := by
      have he : (inner ℝ x ξ - inner ℝ x' ξ' : ℝ) =
          inner ℝ (x - x') ξ + inner ℝ x' (ξ - ξ') := by
        simp only [inner_sub_left, inner_sub_right]
        ring
      rw [he]
      calc
        _ ≤ |inner ℝ (x - x') ξ| + |inner ℝ x' (ξ - ξ')| := abs_add_le _ _
        _ ≤ ‖x - x'‖ * ‖ξ‖ + ‖x'‖ * ‖ξ - ξ'‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
        _ ≤ ‖ξ - ξ'‖ + ‖x - x'‖ := by
          rw [hn]
          have hnx := norm_simplex hx'
          nlinarith [norm_nonneg (ξ - ξ')]
    calc
      _ ≤ α * abs (|inner ℝ x ξ| - |inner ℝ x' ξ'|) :=
        power_lip α hα1.le ⟨abs_nonneg _, inner_bound hx hξ⟩
          ⟨abs_nonneg _, inner_bound hx' hξ'⟩
      _ ≤ α * |inner ℝ x ξ - inner ℝ x' ξ'| :=
        mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le _ _) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by linarith)

#print axioms solution
