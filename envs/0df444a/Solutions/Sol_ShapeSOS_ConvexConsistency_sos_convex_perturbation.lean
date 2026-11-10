-- Prove2me | solution 1 for ShapeSOS.ConvexConsistency.sos_convex_perturbation
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T13:00:51.733214+00:00
-- url     : https://prove2.me/submissions/862ada81-d458-4616-a83b-fa1e2e032417

import Mathlib
import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open Filter MeasureTheory MvPolynomial
open scoped BigOperators Topology MeasureTheory
noncomputable section

namespace ShapeSOS.ConvexConsistency

def ceG : Poly 1 := (X 0 + 1) ^ 3

lemma value_ceG (x : Vec 1) : value ceG x = (x 0 + 1) ^ 3 := by
  simp [value, ceG]

lemma convex_cube_one : Convex ℝ (cube 1 (-1) 1) := by
  intro x hx y hy a b ha hb hab i
  rcases hx i with ⟨hx1, hx2⟩
  rcases hy i with ⟨hy1, hy2⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · calc (-1 : ℝ) = (a + b) * (-1) := by rw [hab, one_mul]
      _ = a * (-1) + b * (-1) := by ring
      _ ≤ a * x i + b * y i := add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
  · calc a * x i + b * y i ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
      _ = (a + b) * 1 := by ring
      _ = 1 := by rw [hab, one_mul]

lemma ceG_convexOn : ConvexOn ℝ (cube 1 (-1) 1) (value ceG) := by
  refine ⟨convex_cube_one, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [value_ceG, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
  have hu : 0 ≤ x 0 + 1 := by linarith [(hx 0).1]
  have hv : 0 ≤ y 0 + 1 := by linarith [(hy 0).1]
  set u : ℝ := x 0 + 1
  set v : ℝ := y 0 + 1
  have hcomb : a * x 0 + b * y 0 + 1 = a * u + b * v := by
    calc a * x 0 + b * y 0 + 1 = a * x 0 + b * y 0 + (a + b) * 1 := by rw [hab, one_mul]
      _ = a * (x 0 + 1) + b * (y 0 + 1) := by ring
  rw [hcomb]
  have hdiff : 0 ≤ a * b * (u - v) ^ 2 * ((2 * a + b) * u + (a + 2 * b) * v) := by positivity
  have hid : a * u ^ 3 + b * v ^ 3 - (a * u + b * v) ^ 3 =
      a * b * (u - v) ^ 2 * ((2 * a + b) * u + (a + 2 * b) * v) := by
    calc a * u ^ 3 + b * v ^ 3 - (a * u + b * v) ^ 3
        = (a + b) ^ 2 * (a * u ^ 3 + b * v ^ 3) - (a * u + b * v) ^ 3 := by rw [hab, one_pow, one_mul]
      _ = a * b * (u - v) ^ 2 * ((2 * a + b) * u + (a + 2 * b) * v) := by ring
  linarith

lemma theta_one_eq (d : ℕ) : theta 1 d = X 0 ^ 2 := by
  unfold theta
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have hemp : Finset.univ.filter (fun j : Fin 1 => (0 : Fin 1) < j) = ∅ := by
    ext j
    simp [Fin.ext_iff]
  rw [hemp, Finset.sum_empty, add_zero]

lemma not_isSOSConvex_ceG (d : ℕ) :
    ¬ RobustPMI.Hierarchy.IsSOSConvex (ceG + MvPolynomial.C (1 : ℝ) * theta 1 d) := by
  rintro ⟨l, T, hT⟩
  have h00 := congr_fun (congr_fun hT 0) 0
  change pderiv 0 (pderiv 0 (ceG + MvPolynomial.C (1 : ℝ) * theta 1 d)) =
    ∑ r : Fin l, T r 0 * T r 0 at h00
  let x₀ : Vec 1 := fun _ => (-2 : ℝ)
  have heval := congr_arg (MvPolynomial.eval x₀) h00
  have hlhs : MvPolynomial.eval x₀
      (pderiv 0 (pderiv 0 (ceG + MvPolynomial.C (1 : ℝ) * theta 1 d))) = -4 := by
    rw [theta_one_eq]
    simp [ceG, x₀, pow_three, pow_two]
    norm_num
  have hrhs : 0 ≤ MvPolynomial.eval x₀ (∑ r : Fin l, T r 0 * T r 0) := by
    rw [map_sum]
    refine Finset.sum_nonneg fun r _ => ?_
    rw [map_mul]
    exact mul_self_nonneg _
  linarith

end ShapeSOS.ConvexConsistency

theorem solution : ¬ (∀ (n : ℕ) (_hn : 0 < n) (g : ShapeSOS.ConvexConsistency.Poly n)
    (_hg : ConvexOn ℝ (ShapeSOS.ConvexConsistency.cube n (-1) 1) (ShapeSOS.ConvexConsistency.value g))
    (ε : ℝ) (_hε : 0 < ε),
    ∃ d₀ : ℕ, ∀ d ≥ d₀, RobustPMI.Hierarchy.IsSOSConvex
      (g + MvPolynomial.C ε * ShapeSOS.ConvexConsistency.theta n d)) := by
  intro hall
  rcases hall 1 Nat.one_pos ShapeSOS.ConvexConsistency.ceG
    ShapeSOS.ConvexConsistency.ceG_convexOn 1 zero_lt_one with ⟨d₀, hd₀⟩
  exact ShapeSOS.ConvexConsistency.not_isSOSConvex_ceG d₀ (hd₀ d₀ (le_refl d₀))
