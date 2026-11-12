-- Prove2me | solution 1 for RobustOpt2009.SDPApproximation.theta_four
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:31:05.943939+00:00
-- url     : https://prove2.me/submissions/baf868e1-1512-4ecc-a6ea-cfa920303758

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Real Set MeasureTheory Filter Topology ModernConvex.MatrixCube
open scoped BigOperators

namespace RobustOpt2009ThetaFourAux

lemma integrable_volume_mul_prod {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    {f : α → ℝ} {g : β → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : α × β => f z.1 * g z.2) := by
  rw [Measure.volume_eq_prod]
  exact hf.mul_prod hg

lemma integral_volume_prod_mul {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    (f : α → ℝ) (g : β → ℝ) :
    (∫ z : α × β, f z.1 * g z.2) = (∫ x : α, f x) * (∫ y : β, g y) := by
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul f g

lemma integral_volume_prod {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SigmaFinite (volume : Measure α)] [SigmaFinite (volume : Measure β)]
    {f : α × β → ℝ} (hf : Integrable f) :
    (∫ z : α × β, f z) = ∫ x : α, ∫ y : β, f (x, y) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact integral_prod f hf

noncomputable def g1 (x : ℝ) : ℝ := (√(2 * π))⁻¹ * exp (-(x ^ 2 / 2))
noncomputable def g2 (p : ℝ × ℝ) : ℝ := g1 p.1 * g1 p.2

lemma g1_nonneg (x : ℝ) : 0 ≤ g1 x := by
  unfold g1
  positivity

lemma g2_nonneg (p : ℝ × ℝ) : 0 ≤ g2 p :=
  mul_nonneg (g1_nonneg _) (g1_nonneg _)

lemma gaussDensity_four_nonneg (u : Fin 4 → ℝ) : 0 ≤ gaussDensity 4 u := by
  unfold gaussDensity
  positivity

lemma integrable_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * exp (-b * x ^ 2)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  simpa [rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq hb hk

lemma integral_sq_mul_gaussian {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * exp (-b * x ^ 2) = (2 * b)⁻¹ * √(π / b) := by
  have hb0 : b ≠ 0 := hb.ne'
  let u : ℝ → ℝ := fun x => x
  let u' : ℝ → ℝ := fun _ => 1
  let v : ℝ → ℝ := fun x => -(2 * b)⁻¹ * exp (-b * x ^ 2)
  let v' : ℝ → ℝ := fun x => x * exp (-b * x ^ 2)
  have hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x := fun x _ => hasDerivAt_id x
  have hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x := by
    intro x _
    refine (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)).congr_deriv ?_
    dsimp [v']
    field_simp
  have huv' : Integrable (u * v') := by
    change Integrable (fun x : ℝ => x * (x * exp (-b * x ^ 2)))
    have h1 : (fun x : ℝ => x * (x * exp (-b * x ^ 2))) =
        fun x : ℝ => x ^ 2 * exp (-b * x ^ 2) := by ext x; ring
    rw [h1]
    exact integrable_pow_mul_exp_neg_mul_sq hb 2
  have hu'v : Integrable (u' * v) := by
    change Integrable (fun x : ℝ => 1 * (-(2 * b)⁻¹ * exp (-b * x ^ 2)))
    simpa using (integrable_exp_neg_mul_sq hb).const_mul (-(2 * b)⁻¹)
  have huv : Integrable (u * v) := by
    change Integrable (fun x : ℝ => x * (-(2 * b)⁻¹ * exp (-b * x ^ 2)))
    have h1 : (fun x : ℝ => x * (-(2 * b)⁻¹ * exp (-b * x ^ 2))) =
        fun x : ℝ => -(2 * b)⁻¹ * (x * exp (-b * x ^ 2)) := by ext x; ring
    rw [h1]
    exact (integrable_mul_exp_neg_mul_sq hb).const_mul _
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv huv' hu'v huv
  have lhs_eq : (∫ x : ℝ, x ^ 2 * exp (-b * x ^ 2)) = ∫ x : ℝ, u x * v' x := by
    congr 1; ext x; dsimp [u, v']; ring
  rw [lhs_eq, hibp]
  have rhs_eq : -∫ x : ℝ, u' x * v x = (2 * b)⁻¹ * ∫ x : ℝ, exp (-b * x ^ 2) := by
    dsimp [u', v]
    simp_rw [one_mul, neg_mul, integral_neg, integral_const_mul, neg_neg]
  rw [rhs_eq, integral_gaussian b]

lemma integrable_g1 : Integrable g1 := by
  have h1 : g1 = fun x : ℝ => (√(2 * π))⁻¹ * (x ^ 0 * exp (-(1 / 2) * x ^ 2)) := by
    ext x; unfold g1
    have he : -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 := by ring
    rw [he]; ring
  rw [h1]
  exact (integrable_pow_mul_exp_neg_mul_sq (by norm_num) 0).const_mul _

lemma integrable_sq_mul_g1 : Integrable (fun x : ℝ => x ^ 2 * g1 x) := by
  have h1 : (fun x : ℝ => x ^ 2 * g1 x) =
      fun x : ℝ => (√(2 * π))⁻¹ * (x ^ 2 * exp (-(1 / 2) * x ^ 2)) := by
    ext x; unfold g1
    have he : -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 := by ring
    rw [he]; ring
  rw [h1]
  exact (integrable_pow_mul_exp_neg_mul_sq (by norm_num) 2).const_mul _

lemma integral_g1 : ∫ x : ℝ, g1 x = 1 := by
  have h1 : (∫ x : ℝ, g1 x) = (√(2 * π))⁻¹ * ∫ x : ℝ, exp (-(1 / 2) * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    have he : -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 := by ring
    rw [he]
  rw [h1, integral_gaussian (1 / 2)]
  have hp : π / (1 / 2 : ℝ) = 2 * π := by ring
  rw [hp, inv_mul_cancel₀ (by positivity)]

lemma integral_sq_mul_g1 : ∫ x : ℝ, x ^ 2 * g1 x = 1 := by
  have h1 : (∫ x : ℝ, x ^ 2 * g1 x) =
      (√(2 * π))⁻¹ * ∫ x : ℝ, x ^ 2 * exp (-(1 / 2) * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    have he : -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 := by ring
    rw [he]; ring
  rw [h1, integral_sq_mul_gaussian (by norm_num : (0 : ℝ) < 1 / 2)]
  have hp : π / (1 / 2 : ℝ) = 2 * π := by ring
  rw [hp]
  have h2 : (2 * (1 / 2 : ℝ))⁻¹ = 1 := by norm_num
  rw [h2, one_mul, inv_mul_cancel₀ (by positivity)]

lemma integral_exp_half_mul_g1 : ∫ x : ℝ, exp (-(x ^ 2 / 2)) * g1 x = (√2)⁻¹ := by
  have h1 : (∫ x : ℝ, exp (-(x ^ 2 / 2)) * g1 x) =
      (√(2 * π))⁻¹ * ∫ x : ℝ, exp (-1 * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    calc
      exp (-(x ^ 2 / 2)) * ((√(2 * π))⁻¹ * exp (-(x ^ 2 / 2))) =
          (√(2 * π))⁻¹ * (exp (-(x ^ 2 / 2)) * exp (-(x ^ 2 / 2))) := by ring
      _ = (√(2 * π))⁻¹ * exp (-1 * x ^ 2) := by rw [← exp_add]; congr 2; ring
  rw [h1, integral_gaussian 1, div_one, sqrt_mul zero_le_two π]
  have hpi : √π ≠ 0 := by positivity
  have h2 : √2 ≠ 0 := by positivity
  field_simp

lemma integral_sq_mul_exp_half_mul_g1 :
    ∫ x : ℝ, x ^ 2 * exp (-(x ^ 2 / 2)) * g1 x = 2⁻¹ * (√2)⁻¹ := by
  have h1 : (∫ x : ℝ, x ^ 2 * exp (-(x ^ 2 / 2)) * g1 x) =
      (√(2 * π))⁻¹ * ∫ x : ℝ, x ^ 2 * exp (-1 * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    calc
      x ^ 2 * exp (-(x ^ 2 / 2)) * ((√(2 * π))⁻¹ * exp (-(x ^ 2 / 2))) =
          (√(2 * π))⁻¹ * (x ^ 2 * (exp (-(x ^ 2 / 2)) * exp (-(x ^ 2 / 2)))) := by ring
      _ = (√(2 * π))⁻¹ * (x ^ 2 * exp (-1 * x ^ 2)) := by rw [← exp_add]; congr 3; ring
  rw [h1, integral_sq_mul_gaussian zero_lt_one, div_one, mul_one, sqrt_mul zero_le_two π]
  have hpi : √π ≠ 0 := by positivity
  have h2 : √2 ≠ 0 := by positivity
  field_simp

lemma integral_exp_39_50_mul_g1 :
    ∫ x : ℝ, exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x = 5 / 8 := by
  have h1 : (∫ x : ℝ, exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x) =
      (√(2 * π))⁻¹ * ∫ x : ℝ, exp (-(32 / 25 : ℝ) * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    calc
      exp (-(39 / 50 : ℝ) * x ^ 2) * ((√(2 * π))⁻¹ * exp (-(x ^ 2 / 2))) =
          (√(2 * π))⁻¹ * (exp (-(39 / 50 : ℝ) * x ^ 2) * exp (-(x ^ 2 / 2))) := by ring
      _ = (√(2 * π))⁻¹ * exp (-(32 / 25 : ℝ) * x ^ 2) := by rw [← exp_add]; congr 2; ring
  rw [h1, integral_gaussian (32 / 25 : ℝ)]
  have hsqrt : √(π / (32 / 25 : ℝ)) = (5 / 8 : ℝ) * √(2 * π) := by
    have hp : π / (32 / 25 : ℝ) = (5 / 8 : ℝ) ^ 2 * (2 * π) := by ring
    rw [hp, sqrt_mul (by positivity : (0 : ℝ) ≤ (5 / 8 : ℝ) ^ 2), sqrt_sq (by positivity)]
  rw [hsqrt]
  have h2pi : √(2 * π) ≠ 0 := by positivity
  field_simp

lemma integral_sq_mul_exp_39_50_mul_g1 :
    ∫ x : ℝ, x ^ 2 * exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x = 125 / 512 := by
  have h1 : (∫ x : ℝ, x ^ 2 * exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x) =
      (√(2 * π))⁻¹ * ∫ x : ℝ, x ^ 2 * exp (-(32 / 25 : ℝ) * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1; ext x; unfold g1
    calc
      x ^ 2 * exp (-(39 / 50 : ℝ) * x ^ 2) * ((√(2 * π))⁻¹ * exp (-(x ^ 2 / 2))) =
          (√(2 * π))⁻¹ * (x ^ 2 * (exp (-(39 / 50 : ℝ) * x ^ 2) * exp (-(x ^ 2 / 2)))) := by ring
      _ = (√(2 * π))⁻¹ * (x ^ 2 * exp (-(32 / 25 : ℝ) * x ^ 2)) := by
          rw [← exp_add]; congr 3; ring
  rw [h1, integral_sq_mul_gaussian (by norm_num : (0 : ℝ) < 32 / 25)]
  have hsqrt : √(π / (32 / 25 : ℝ)) = (5 / 8 : ℝ) * √(2 * π) := by
    have hp : π / (32 / 25 : ℝ) = (5 / 8 : ℝ) ^ 2 * (2 * π) := by ring
    rw [hp, sqrt_mul (by positivity : (0 : ℝ) ≤ (5 / 8 : ℝ) ^ 2), sqrt_sq (by positivity)]
  rw [hsqrt]
  have h2pi : √(2 * π) ≠ 0 := by positivity
  field_simp
  norm_num

lemma g2_eq (q : ℝ × ℝ) : g2 q = (2 * π)⁻¹ * exp (-(q.1 ^ 2 + q.2 ^ 2) / 2) := by
  dsimp [g2, g1]
  have hsqrt : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = (2 * π)⁻¹ := by
    rw [← mul_inv, mul_self_sqrt (by positivity)]
  have hexp : exp (-(q.1 ^ 2 / 2)) * exp (-(q.2 ^ 2 / 2)) = exp (-(q.1 ^ 2 + q.2 ^ 2) / 2) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    (√(2 * π))⁻¹ * exp (-(q.1 ^ 2 / 2)) * ((√(2 * π))⁻¹ * exp (-(q.2 ^ 2 / 2)))
        = ((√(2 * π))⁻¹ * (√(2 * π))⁻¹) * (exp (-(q.1 ^ 2 / 2)) * exp (-(q.2 ^ 2 / 2))) := by ring
    _ = (2 * π)⁻¹ * exp (-(q.1 ^ 2 + q.2 ^ 2) / 2) := by rw [hsqrt, hexp]

lemma integrable_g2 : Integrable g2 :=
  integrable_volume_mul_prod integrable_g1 integrable_g1

lemma integrable_fst_sq_g2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * g2 p) := by
  have h : (fun p : ℝ × ℝ => p.1 ^ 2 * g2 p) = fun p => (p.1 ^ 2 * g1 p.1) * g1 p.2 := by
    ext p; unfold g2; ring
  rw [h]
  exact integrable_volume_mul_prod integrable_sq_mul_g1 integrable_g1

lemma integrable_snd_sq_g2 : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * g2 p) := by
  have h : (fun p : ℝ × ℝ => p.2 ^ 2 * g2 p) = fun p => g1 p.1 * (p.2 ^ 2 * g1 p.2) := by
    ext p; unfold g2; ring
  rw [h]
  exact integrable_volume_mul_prod integrable_g1 integrable_sq_mul_g1

lemma integrable_normSq_g2 : Integrable (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * g2 p) := by
  have h : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * g2 p) =
      fun p => p.1 ^ 2 * g2 p + p.2 ^ 2 * g2 p := by ext p; ring
  rw [h]
  exact integrable_fst_sq_g2.add integrable_snd_sq_g2

lemma integral_g2 : ∫ p : ℝ × ℝ, g2 p = 1 := by
  unfold g2
  rw [integral_volume_prod_mul, integral_g1, mul_one]

lemma integral_fst_sq_g2 : ∫ p : ℝ × ℝ, p.1 ^ 2 * g2 p = 1 := by
  have h : (fun p : ℝ × ℝ => p.1 ^ 2 * g2 p) = fun p => (p.1 ^ 2 * g1 p.1) * g1 p.2 := by
    ext p; unfold g2; ring
  rw [h, integral_volume_prod_mul (fun x => x ^ 2 * g1 x) g1,
    integral_sq_mul_g1, integral_g1, mul_one]

lemma integral_snd_sq_g2 : ∫ p : ℝ × ℝ, p.2 ^ 2 * g2 p = 1 := by
  have h : (fun p : ℝ × ℝ => p.2 ^ 2 * g2 p) = fun p => g1 p.1 * (p.2 ^ 2 * g1 p.2) := by
    ext p; unfold g2; ring
  rw [h, integral_volume_prod_mul g1 (fun x => x ^ 2 * g1 x),
    integral_g1, integral_sq_mul_g1, mul_one]

lemma integral_normSq_g2 : ∫ p : ℝ × ℝ, (p.1 ^ 2 + p.2 ^ 2) * g2 p = 2 := by
  have h : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * g2 p) =
      fun p => p.1 ^ 2 * g2 p + p.2 ^ 2 * g2 p := by ext p; ring
  rw [h, integral_add integrable_fst_sq_g2 integrable_snd_sq_g2,
    integral_fst_sq_g2, integral_snd_sq_g2]
  norm_num

lemma integral_exp_half_g2 :
    ∫ p : ℝ × ℝ, exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p = 1 / 2 := by
  have h : (fun p : ℝ × ℝ => exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) =
      fun p => (exp (-(p.1 ^ 2 / 2)) * g1 p.1) * (exp (-(p.2 ^ 2 / 2)) * g1 p.2) := by
    ext p; unfold g2
    have he : -(p.1 ^ 2 + p.2 ^ 2) / 2 = -(p.1 ^ 2 / 2) + -(p.2 ^ 2 / 2) := by ring
    rw [he, exp_add]; ring
  rw [h, integral_volume_prod_mul (fun x => exp (-(x ^ 2 / 2)) * g1 x)
    (fun x => exp (-(x ^ 2 / 2)) * g1 x),
    integral_exp_half_mul_g1, ← mul_inv, mul_self_sqrt zero_le_two]
  norm_num

lemma integrable_exp_half_g2 :
    Integrable (fun p : ℝ × ℝ => exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) := by
  refine integrable_g2.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    unfold g2 g1
    fun_prop
  · filter_upwards with p
    have hle : exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (g2_nonneg p))]
    exact mul_le_of_le_one_left (g2_nonneg p) hle

lemma integrable_normSq_exp_half_g2 :
    Integrable (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) := by
  refine integrable_normSq_g2.mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    unfold g2 g1
    fun_prop
  · filter_upwards with p
    have hnn : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
    have hle : exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) ≤ 1 :=
      exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hnn (exp_pos _).le) (g2_nonneg p))]
    calc
      (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p =
          exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * ((p.1 ^ 2 + p.2 ^ 2) * g2 p) := by ring
      _ ≤ 1 * ((p.1 ^ 2 + p.2 ^ 2) * g2 p) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hnn (g2_nonneg p))
      _ = (p.1 ^ 2 + p.2 ^ 2) * g2 p := one_mul _

lemma integral_normSq_exp_half_g2 :
    ∫ p : ℝ × ℝ, (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p = 1 / 2 := by
  have hfst : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) := by
    refine integrable_fst_sq_g2.mono' (by unfold g2 g1; exact Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with p
    have hle : exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le) (g2_nonneg p))]
    calc
      p.1 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p =
          exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * (p.1 ^ 2 * g2 p) := by ring
      _ ≤ 1 * (p.1 ^ 2 * g2 p) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg _) (g2_nonneg p))
      _ = p.1 ^ 2 * g2 p := one_mul _
  have hsnd : Integrable (fun p : ℝ × ℝ => p.2 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) := by
    refine integrable_snd_sq_g2.mono' (by unfold g2 g1; exact Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with p
    have hle : exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le) (g2_nonneg p))]
    calc
      p.2 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p =
          exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * (p.2 ^ 2 * g2 p) := by ring
      _ ≤ 1 * (p.2 ^ 2 * g2 p) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (sq_nonneg _) (g2_nonneg p))
      _ = p.2 ^ 2 * g2 p := one_mul _
  have hsplit : (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) =
      fun p => p.1 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p +
        p.2 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p := by ext p; ring
  rw [hsplit, integral_add hfst hsnd]
  have h1 : (∫ p : ℝ × ℝ, p.1 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) = 1 / 4 := by
    have hf : (fun p : ℝ × ℝ => p.1 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) =
        fun p => (p.1 ^ 2 * exp (-(p.1 ^ 2 / 2)) * g1 p.1) * (exp (-(p.2 ^ 2 / 2)) * g1 p.2) := by
      ext p; unfold g2
      have he : -(p.1 ^ 2 + p.2 ^ 2) / 2 = -(p.1 ^ 2 / 2) + -(p.2 ^ 2 / 2) := by ring
      rw [he, exp_add]; ring
    rw [hf, integral_volume_prod_mul (fun x => x ^ 2 * exp (-(x ^ 2 / 2)) * g1 x)
      (fun x => exp (-(x ^ 2 / 2)) * g1 x),
      integral_sq_mul_exp_half_mul_g1, integral_exp_half_mul_g1,
      mul_assoc, ← mul_inv, mul_self_sqrt zero_le_two]
    norm_num
  have h2 : (∫ p : ℝ × ℝ, p.2 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) = 1 / 4 := by
    have hf : (fun p : ℝ × ℝ => p.2 ^ 2 * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) =
        fun p => (exp (-(p.1 ^ 2 / 2)) * g1 p.1) * (p.2 ^ 2 * exp (-(p.2 ^ 2 / 2)) * g1 p.2) := by
      ext p; unfold g2
      have he : -(p.1 ^ 2 + p.2 ^ 2) / 2 = -(p.1 ^ 2 / 2) + -(p.2 ^ 2 / 2) := by ring
      rw [he, exp_add]; ring
    rw [hf, integral_volume_prod_mul (fun x => exp (-(x ^ 2 / 2)) * g1 x)
      (fun x => x ^ 2 * exp (-(x ^ 2 / 2)) * g1 x),
      integral_exp_half_mul_g1, integral_sq_mul_exp_half_mul_g1,
      ← mul_assoc, mul_comm (√2)⁻¹ (2⁻¹), mul_assoc, ← mul_inv, mul_self_sqrt zero_le_two]
    norm_num
  rw [h1, h2]
  norm_num

lemma integral_Ioi_r_exp (a : ℝ) :
    ∫ r in Ioi a, r * exp (-(r ^ 2 / 2)) = exp (-(a ^ 2 / 2)) := by
  have hderiv : ∀ r ∈ Ici a, HasDerivAt (fun r : ℝ => -exp (-(r ^ 2 / 2)))
      (r * exp (-(r ^ 2 / 2))) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2 / 2)) (-r) r :=
      (((hasDerivAt_pow 2 r).div_const 2).neg).congr_deriv (by ring)
    exact (h1.exp.neg).congr_deriv (by ring)
  have hint : IntegrableOn (fun r : ℝ => r * exp (-(r ^ 2 / 2))) (Ioi a) := by
    have h1 : (fun r : ℝ => r * exp (-(r ^ 2 / 2))) =
        fun r : ℝ => r ^ 1 * exp (-(1 / 2) * r ^ 2) := by
      ext r; simp only [pow_one]; congr 1; congr 1; ring
    rw [h1]
    exact (integrable_pow_mul_exp_neg_mul_sq (by norm_num) 1).integrableOn
  have htend : Tendsto (fun r : ℝ => -exp (-(r ^ 2 / 2))) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 by norm_num]
    refine Filter.Tendsto.neg ?_
    have h1 : (fun r : ℝ => exp (-(r ^ 2 / 2))) = fun r : ℝ => exp ((-1 / 2) * r ^ 2) := by
      ext r; congr 1; ring
    rw [h1]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num))
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend

lemma integral_Ioi_r3_exp (a : ℝ) :
    ∫ r in Ioi a, r ^ 3 * exp (-(r ^ 2 / 2)) = (a ^ 2 + 2) * exp (-(a ^ 2 / 2)) := by
  have hderiv : ∀ r ∈ Ici a, HasDerivAt (fun r : ℝ => (-(r ^ 2 + 2)) * exp (-(r ^ 2 / 2)))
      (r ^ 3 * exp (-(r ^ 2 / 2))) r := by
    intro r _
    have hp : HasDerivAt (fun r : ℝ => -(r ^ 2 + 2)) (-(2 * r)) r :=
      (((hasDerivAt_pow 2 r).add_const 2).neg).congr_deriv (by ring)
    have he : HasDerivAt (fun r : ℝ => exp (-(r ^ 2 / 2))) (-r * exp (-(r ^ 2 / 2))) r := by
      have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2 / 2)) (-r) r :=
        (((hasDerivAt_pow 2 r).div_const 2).neg).congr_deriv (by ring)
      exact h1.exp.congr_deriv (by ring)
    exact (hp.mul he).congr_deriv (by ring)
  have hint : IntegrableOn (fun r : ℝ => r ^ 3 * exp (-(r ^ 2 / 2))) (Ioi a) := by
    have h1 : (fun r : ℝ => r ^ 3 * exp (-(r ^ 2 / 2))) =
        fun r : ℝ => r ^ 3 * exp (-(1 / 2) * r ^ 2) := by
      ext r; congr 1; congr 1; ring
    rw [h1]
    exact (integrable_pow_mul_exp_neg_mul_sq (by norm_num) 3).integrableOn
  have htend : Tendsto (fun r : ℝ => (-(r ^ 2 + 2)) * exp (-(r ^ 2 / 2))) atTop (𝓝 0) := by
    have hexp0 : Tendsto (fun x : ℝ => exp (-(1 / 2) * x)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have hr2 : Tendsto (fun r : ℝ => r ^ 2 * exp (-(1 / 2) * r ^ 2)) atTop (𝓝 0) := by
      simpa [rpow_two] using
        (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2) 2).tendsto_zero_of_tendsto hexp0
    have hr0 : Tendsto (fun r : ℝ => exp (-(1 / 2) * r ^ 2)) atTop (𝓝 0) := by
      simpa using
        (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1 / 2) 0).tendsto_zero_of_tendsto hexp0
    have hcomb : (fun r : ℝ => (-(r ^ 2 + 2)) * exp (-(r ^ 2 / 2))) =
        fun r : ℝ => -(r ^ 2 * exp (-(1 / 2) * r ^ 2)) - 2 * exp (-(1 / 2) * r ^ 2) := by
      ext r
      have heq : -(r ^ 2 / 2) = -(1 / 2) * r ^ 2 := by ring
      rw [heq]; ring
    rw [hcomb, show (0 : ℝ) = -0 - 2 * 0 by norm_num]
    exact hr2.neg.sub (hr0.const_mul 2)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  linarith

lemma integral_tail_g2 {t : ℝ} (ht : 0 ≤ t) :
    ∫ q : ℝ × ℝ, (if t ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q = exp (-t / 2) := by
  rw [← integral_comp_polarCoord_symm, polarCoord_target]
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • ((if t ≤ (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 then (1 : ℝ) else 0) *
        g2 (polarCoord.symm p)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ((if √t ≤ p.1 then p.1 * exp (-(p.1 ^ 2 / 2)) else 0) * (2 * π)⁻¹) := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    dsimp only at hr ⊢
    rw [g2_eq]
    simp only [polarCoord_symm_apply]
    have hr2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      calc
        (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
        _ = r ^ 2 := by rw [cos_sq_add_sin_sq, mul_one]
    rw [hr2, show -(r ^ 2) / 2 = -(r ^ 2 / 2) by ring]
    have hiff : (t ≤ r ^ 2) ↔ (√t ≤ r) := by
      conv_lhs => rw [← sq_sqrt ht]
      exact sq_le_sq₀ (sqrt_nonneg t) (le_of_lt hr)
    simp only [hiff, smul_eq_mul]
    split_ifs <;> ring
  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ((if √t ≤ p.1 then p.1 * exp (-(p.1 ^ 2 / 2)) else 0) * (2 * π)⁻¹)) =
      (∫ r in Ioi (0 : ℝ), if √t ≤ r then r * exp (-(r ^ 2 / 2)) else 0) *
        (∫ _ in Ioo (-π) π, (2 * π)⁻¹) := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod_mul
      (fun r : ℝ => if √t ≤ r then r * exp (-(r ^ 2 / 2)) else 0)
      (fun _ : ℝ => (2 * π)⁻¹) (Ioi (0 : ℝ)) (Ioo (-π) π)
  rw [hcongr, hprod]
  have hθ : ∫ _ in Ioo (-π) π, (2 * π)⁻¹ = 1 := by
    rw [setIntegral_const, Measure.real, volume_Ioo, ENNReal.toReal_ofReal (by linarith [pi_pos]),
      smul_eq_mul, show π - -π = 2 * π by ring, mul_inv_cancel₀ (by positivity)]
  rw [hθ, mul_one]
  have hae : (fun r : ℝ => if √t ≤ r then r * exp (-(r ^ 2 / 2)) else 0) =ᵐ[volume.restrict (Ioi 0)]
      (Ioi (√t)).indicator (fun r : ℝ => r * exp (-(r ^ 2 / 2))) := by
    refine ae_restrict_of_ae ?_
    have h1 : (fun r : ℝ => if √t ≤ r then r * exp (-(r ^ 2 / 2)) else 0) =
        (Ici (√t)).indicator (fun r : ℝ => r * exp (-(r ^ 2 / 2))) := by
      ext r; simp [Set.indicator, mem_Ici]
    rw [h1]
    exact indicator_ae_eq_of_ae_eq_set Ioi_ae_eq_Ici.symm
  rw [integral_congr_ae hae, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    max_eq_right (sqrt_nonneg t), integral_Ioi_r_exp, sq_sqrt ht, neg_div]

lemma integral_tail_normSq_g2 {t : ℝ} (ht : 0 ≤ t) :
    ∫ q : ℝ × ℝ, (q.1 ^ 2 + q.2 ^ 2) * (if t ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q =
      (t + 2) * exp (-t / 2) := by
  rw [← integral_comp_polarCoord_symm, polarCoord_target]
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • (((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) *
        (if t ≤ (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 then (1 : ℝ) else 0) *
        g2 (polarCoord.symm p)) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        ((if √t ≤ p.1 then p.1 ^ 3 * exp (-(p.1 ^ 2 / 2)) else 0) * (2 * π)⁻¹) := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨hr, _⟩
    dsimp only at hr ⊢
    rw [g2_eq]
    simp only [polarCoord_symm_apply]
    have hr2 : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
      calc
        (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 * (cos θ ^ 2 + sin θ ^ 2) := by ring
        _ = r ^ 2 := by rw [cos_sq_add_sin_sq, mul_one]
    rw [hr2, show -(r ^ 2) / 2 = -(r ^ 2 / 2) by ring]
    have hiff : (t ≤ r ^ 2) ↔ (√t ≤ r) := by
      conv_lhs => rw [← sq_sqrt ht]
      exact sq_le_sq₀ (sqrt_nonneg t) (le_of_lt hr)
    simp only [hiff, smul_eq_mul]
    split_ifs <;> ring
  have hprod : (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      ((if √t ≤ p.1 then p.1 ^ 3 * exp (-(p.1 ^ 2 / 2)) else 0) * (2 * π)⁻¹)) =
      (∫ r in Ioi (0 : ℝ), if √t ≤ r then r ^ 3 * exp (-(r ^ 2 / 2)) else 0) *
        (∫ _ in Ioo (-π) π, (2 * π)⁻¹) := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod_mul
      (fun r : ℝ => if √t ≤ r then r ^ 3 * exp (-(r ^ 2 / 2)) else 0)
      (fun _ : ℝ => (2 * π)⁻¹) (Ioi (0 : ℝ)) (Ioo (-π) π)
  rw [hcongr, hprod]
  have hθ : ∫ _ in Ioo (-π) π, (2 * π)⁻¹ = 1 := by
    rw [setIntegral_const, Measure.real, volume_Ioo, ENNReal.toReal_ofReal (by linarith [pi_pos]),
      smul_eq_mul, show π - -π = 2 * π by ring, mul_inv_cancel₀ (by positivity)]
  rw [hθ, mul_one]
  have hae : (fun r : ℝ => if √t ≤ r then r ^ 3 * exp (-(r ^ 2 / 2)) else 0) =ᵐ[volume.restrict (Ioi 0)]
      (Ioi (√t)).indicator (fun r : ℝ => r ^ 3 * exp (-(r ^ 2 / 2))) := by
    refine ae_restrict_of_ae ?_
    have h1 : (fun r : ℝ => if √t ≤ r then r ^ 3 * exp (-(r ^ 2 / 2)) else 0) =
        (Ici (√t)).indicator (fun r : ℝ => r ^ 3 * exp (-(r ^ 2 / 2))) := by
      ext r; simp [Set.indicator, mem_Ici]
    rw [h1]
    exact indicator_ae_eq_of_ae_eq_set Ioi_ae_eq_Ici.symm
  rw [integral_congr_ae hae, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
    max_eq_right (sqrt_nonneg t), integral_Ioi_r3_exp, sq_sqrt ht, neg_div]

noncomputable def fin4Equiv : MeasurableEquiv (Fin 4 → ℝ) ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ) finSumFinEquiv.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow)

lemma measurePreserving_fin4Equiv : MeasurePreserving fin4Equiv volume volume := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ) finSumFinEquiv.symm)
      volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 2 ⊕ Fin 2 => ℝ) finSumFinEquiv.symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)) volume volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr
        (MeasurableEquiv.finTwoArrow (α := ℝ))
        (MeasurableEquiv.finTwoArrow (α := ℝ))) volume volume :=
    (volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)
  exact (h1.trans h2).trans h3

lemma fin4Equiv_symm_apply (pq : (ℝ × ℝ) × (ℝ × ℝ)) :
    fin4Equiv.symm pq = ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] := by
  apply fin4Equiv.injective
  rw [fin4Equiv.apply_symm_apply]
  rcases pq with ⟨⟨x0, x1⟩, ⟨x2, x3⟩⟩
  simp [fin4Equiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

lemma integral_fin4 (f : (Fin 4 → ℝ) → ℝ) :
    (∫ u : Fin 4 → ℝ, f u) = ∫ pq : (ℝ × ℝ) × (ℝ × ℝ), f ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] := by
  rw [← measurePreserving_fin4Equiv.symm.integral_comp fin4Equiv.symm.measurableEmbedding]
  simp only [fin4Equiv_symm_apply]

lemma integrable_fin4_iff (f : (Fin 4 → ℝ) → ℝ) :
    Integrable f ↔ Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => f ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) := by
  rw [← measurePreserving_fin4Equiv.symm.integrable_comp_emb fin4Equiv.symm.measurableEmbedding]
  simp only [Function.comp_def, fin4Equiv_symm_apply]

lemma integral_perm (σ : Equiv.Perm (Fin 4)) (f : (Fin 4 → ℝ) → ℝ) :
    (∫ u : Fin 4 → ℝ, f (u ∘ σ)) = ∫ u : Fin 4 → ℝ, f u := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) σ.symm
  have hmp : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) σ.symm
  have he : ∀ u : Fin 4 → ℝ, e u = u ∘ σ := by
    intro u; ext i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa [he] using hmp.integral_comp e.measurableEmbedding f

lemma integrable_perm_iff (σ : Equiv.Perm (Fin 4)) (f : (Fin 4 → ℝ) → ℝ) :
    Integrable (fun u : Fin 4 → ℝ => f (u ∘ σ)) ↔ Integrable f := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ) σ.symm
  have hmp : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ) σ.symm
  have he : ∀ u : Fin 4 → ℝ, e u = u ∘ σ := by
    intro u; ext i
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa [Function.comp_def, he] using (hmp.integrable_comp_emb e.measurableEmbedding (g := f))

lemma gaussDensity_four_comp_perm (σ : Equiv.Perm (Fin 4)) (u : Fin 4 → ℝ) :
    gaussDensity 4 (u ∘ σ) = gaussDensity 4 u := by
  unfold gaussDensity
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => u i ^ 2)]

lemma gaussDensity_four_vec (p q : ℝ × ℝ) :
    gaussDensity 4 ![p.1, p.2, q.1, q.2] = g2 p * g2 q := by
  unfold gaussDensity
  rw [g2_eq, g2_eq, Fin.sum_univ_four]
  simp only [Nat.cast_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hp : (2 * π) ^ (-(4 : ℝ) / 2) = (2 * π)⁻¹ * (2 * π)⁻¹ := by
    have hexp : -(4 : ℝ) / 2 = ((-2 : ℤ) : ℝ) := by norm_num
    rw [hexp, rpow_intCast]
    have h2pi : 2 * π ≠ 0 := by positivity
    field_simp
  rw [hp]
  have he : -(p.1 ^ 2 + p.2 ^ 2 + q.1 ^ 2 + q.2 ^ 2) / 2 =
      -(p.1 ^ 2 + p.2 ^ 2) / 2 + -(q.1 ^ 2 + q.2 ^ 2) / 2 := by ring
  rw [he, exp_add]
  ring

lemma thetaIntegral_neg (α : Fin 4 → ℝ) : thetaIntegral 4 (-α) = thetaIntegral 4 α := by
  unfold thetaIntegral
  congr 1; ext u; congr 1
  have h : (∑ i : Fin 4, (-α) i * u i ^ 2) = -(∑ i : Fin 4, α i * u i ^ 2) := by
    simp [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [h, abs_neg]

lemma thetaIntegral_perm (σ : Equiv.Perm (Fin 4)) (α : Fin 4 → ℝ) :
    thetaIntegral 4 (α ∘ σ) = thetaIntegral 4 α := by
  unfold thetaIntegral
  rw [← integral_perm σ]
  congr 1; ext u
  rw [gaussDensity_four_comp_perm]
  congr 2
  exact Equiv.sum_comp σ (fun i => α i * u i ^ 2)

lemma measurable_gaussDensity_four : Measurable (gaussDensity 4) := by
  unfold gaussDensity
  fun_prop

lemma integrable_coord_sq_gauss (i : Fin 4) :
    Integrable (fun u : Fin 4 → ℝ => u i ^ 2 * gaussDensity 4 u) := by
  have h0 : Integrable (fun u : Fin 4 → ℝ => u 0 ^ 2 * gaussDensity 4 u) := by
    rw [integrable_fin4_iff]
    have h : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 0 ^ 2 *
          gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
        fun pq => (pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2 := by
      ext pq
      rw [gaussDensity_four_vec]
      simp [mul_assoc]
    rw [h]
    exact integrable_volume_mul_prod integrable_fst_sq_g2 integrable_g2
  rw [← integrable_perm_iff (Equiv.swap 0 i)]
  simpa [gaussDensity_four_comp_perm] using h0

lemma integral_coord_sq_gauss (i : Fin 4) :
    ∫ u : Fin 4 → ℝ, u i ^ 2 * gaussDensity 4 u = 1 := by
  rw [← integral_perm (Equiv.swap 0 i)]
  have h : (fun u : Fin 4 → ℝ => (u ∘ Equiv.swap 0 i) i ^ 2 * gaussDensity 4 (u ∘ Equiv.swap 0 i)) =
      fun u => u 0 ^ 2 * gaussDensity 4 u := by
    ext u; simp [gaussDensity_four_comp_perm]
  rw [h, integral_fin4]
  have h2 : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 0 ^ 2 *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => (pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2 := by
    ext pq; rw [gaussDensity_four_vec]; simp [mul_assoc]
  rw [h2, integral_volume_prod_mul (fun p : ℝ × ℝ => p.1 ^ 2 * g2 p) g2,
    integral_fst_sq_g2, integral_g2, mul_one]

lemma integrable_coord_sq_witness_gauss (i : Fin 4) (H : (Fin 4 → ℝ) → ℝ)
    (hH_meas : Measurable H) (hH_bdd : ∀ u, |H u| ≤ 1) :
    Integrable (fun u : Fin 4 → ℝ => u i ^ 2 * H u * gaussDensity 4 u) := by
  refine (integrable_coord_sq_gauss i).mono' ?_ ?_
  · exact (((measurable_pi_apply i).pow_const 2).mul hH_meas |>.mul
      measurable_gaussDensity_four).aestronglyMeasurable
  · filter_upwards with u
    have hg := gaussDensity_four_nonneg u
    have hu2 : 0 ≤ u i ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hu2, abs_of_nonneg hg]
    calc
      u i ^ 2 * |H u| * gaussDensity 4 u ≤ u i ^ 2 * 1 * gaussDensity 4 u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hH_bdd u) hu2) hg
      _ = u i ^ 2 * gaussDensity 4 u := by ring

lemma thetaIntegral_ge_of_witness (α : Fin 4 → ℝ) (H : (Fin 4 → ℝ) → ℝ)
    (hH_meas : Measurable H) (hH_bdd : ∀ u, |H u| ≤ 1) :
    (∑ i : Fin 4, α i * ∫ u : Fin 4 → ℝ, u i ^ 2 * H u * gaussDensity 4 u) ≤
      thetaIntegral 4 α := by
  have hint_term : ∀ i : Fin 4,
      Integrable (fun u : Fin 4 → ℝ => α i * (u i ^ 2 * H u * gaussDensity 4 u)) :=
    fun i => (integrable_coord_sq_witness_gauss i H hH_meas hH_bdd).const_mul (α i)
  have hint_lhs : Integrable (fun u : Fin 4 → ℝ =>
      ∑ i : Fin 4, α i * (u i ^ 2 * H u * gaussDensity 4 u)) :=
    integrable_finsetSum Finset.univ fun i _ => hint_term i
  have hint_rhs : Integrable (fun u : Fin 4 → ℝ =>
      |∑ i : Fin 4, α i * u i ^ 2| * gaussDensity 4 u) := by
    have hdom : Integrable (fun u : Fin 4 → ℝ =>
        ∑ i : Fin 4, |α i| * (u i ^ 2 * gaussDensity 4 u)) :=
      integrable_finsetSum Finset.univ fun i _ => (integrable_coord_sq_gauss i).const_mul |α i|
    refine hdom.mono' ?_ ?_
    · have hm : Measurable (fun u : Fin 4 → ℝ => ∑ i : Fin 4, α i * u i ^ 2) := by fun_prop
      exact (hm.abs.mul measurable_gaussDensity_four).aestronglyMeasurable
    · filter_upwards with u
      have hg := gaussDensity_four_nonneg u
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hg]
      calc
        |∑ i : Fin 4, α i * u i ^ 2| * gaussDensity 4 u ≤
            (∑ i : Fin 4, |α i * u i ^ 2|) * gaussDensity 4 u :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hg
        _ = ∑ i : Fin 4, |α i| * (u i ^ 2 * gaussDensity 4 u) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sq_nonneg (u i)), mul_assoc]
  unfold thetaIntegral
  calc
    (∑ i : Fin 4, α i * ∫ u : Fin 4 → ℝ, u i ^ 2 * H u * gaussDensity 4 u) =
        ∑ i : Fin 4, ∫ u : Fin 4 → ℝ, α i * (u i ^ 2 * H u * gaussDensity 4 u) := by
      refine Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    _ = ∫ u : Fin 4 → ℝ, ∑ i : Fin 4, α i * (u i ^ 2 * H u * gaussDensity 4 u) :=
      (integral_finsetSum Finset.univ fun i _ => hint_term i).symm
    _ ≤ ∫ u : Fin 4 → ℝ, |∑ i : Fin 4, α i * u i ^ 2| * gaussDensity 4 u := by
      refine integral_mono hint_lhs hint_rhs fun u => ?_
      have hg := gaussDensity_four_nonneg u
      have hfactor : (∑ i : Fin 4, α i * (u i ^ 2 * H u * gaussDensity 4 u)) =
          ((∑ i : Fin 4, α i * u i ^ 2) * H u) * gaussDensity 4 u := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hfactor]
      refine mul_le_mul_of_nonneg_right ?_ hg
      calc
        (∑ i : Fin 4, α i * u i ^ 2) * H u ≤ |(∑ i : Fin 4, α i * u i ^ 2) * H u| :=
          le_abs_self _
        _ = |∑ i : Fin 4, α i * u i ^ 2| * |H u| := abs_mul _ _
        _ ≤ |∑ i : Fin 4, α i * u i ^ 2| * 1 :=
          mul_le_mul_of_nonneg_left (hH_bdd u) (abs_nonneg _)
        _ = |∑ i : Fin 4, α i * u i ^ 2| := mul_one _

/-! ### Case (4, 0) -/

lemma case_4_0 (α : Fin 4 → ℝ) (h0 : 0 ≤ α 0) (h1 : 0 ≤ α 1) (h2 : 0 ≤ α 2) (h3 : 0 ≤ α 3) :
    (1 / 2 : ℝ) * (∑ i : Fin 4, |α i|) ≤ thetaIntegral 4 α := by
  have hw := thetaIntegral_ge_of_witness α (fun _ => 1) measurable_const (by intro _; norm_num)
  simp only [mul_one, integral_coord_sq_gauss] at hw
  rw [Fin.sum_univ_four] at hw ⊢
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h3]
  linarith

/-! ### Case (2, 2) and Attainment at `α*` -/

noncomputable def H22 (u : Fin 4 → ℝ) : ℝ :=
  1 - 2 * (if u 0 ^ 2 + u 1 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2 then (1 : ℝ) else 0)

lemma measurable_H22 : Measurable H22 := by
  have hm : MeasurableSet {u : Fin 4 → ℝ | u 0 ^ 2 + u 1 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have h : (fun u : Fin 4 → ℝ => if u 0 ^ 2 + u 1 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2 then (1 : ℝ) else 0) =
      {u : Fin 4 → ℝ | u 0 ^ 2 + u 1 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2}.indicator (fun _ => 1) := by
    ext u; simp [Set.indicator]
  unfold H22
  exact measurable_const.sub (measurable_const.mul (h ▸ measurable_const.indicator hm))

lemma abs_H22_le (u : Fin 4 → ℝ) : |H22 u| ≤ 1 := by
  unfold H22
  split_ifs <;> norm_num

lemma integral_U_H22 :
    ∫ u : Fin 4 → ℝ, (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u = 1 := by
  rw [integral_fin4]
  have hm : MeasurableSet {pq : (ℝ × ℝ) × (ℝ × ℝ) | pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hint_prod : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2) :=
    integrable_volume_mul_prod integrable_normSq_g2 integrable_g2
  have hint_ind : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
        (((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2)) := by
    have heq : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2)) =
        {pq : (ℝ × ℝ) × (ℝ × ℝ) | pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2}.indicator
          (fun pq => ((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2) := by
      ext pq; simp [Set.indicator]
    rw [heq]
    exact hint_prod.indicator hm
  have hsplit : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 0 ^ 2 +
        (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 1 ^ 2) *
        H22 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => ((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2 -
        2 * ((if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (((pq.1.1 ^ 2 + pq.1.2 ^ 2) * g2 pq.1) * g2 pq.2)) := by
    ext pq
    unfold H22
    rw [gaussDensity_four_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    by_cases hcond : pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 <;> simp [hcond] <;> ring
  rw [hsplit, integral_sub hint_prod (hint_ind.const_mul 2), integral_const_mul,
    integral_volume_prod_mul (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2) * g2 p) g2,
    integral_normSq_g2, integral_g2, mul_one,
    integral_volume_prod hint_ind]
  have hinner : ∀ p : ℝ × ℝ,
      (∫ q : ℝ × ℝ, (if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (((p.1 ^ 2 + p.2 ^ 2) * g2 p) * g2 q)) =
      (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p := by
    intro p
    have hf : (fun q : ℝ × ℝ => (if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (((p.1 ^ 2 + p.2 ^ 2) * g2 p) * g2 q)) =
        fun q => ((p.1 ^ 2 + p.2 ^ 2) * g2 p) *
          ((if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q) := by
      ext q; ring
    rw [hf, integral_const_mul, integral_tail_g2 (by positivity)]
    ring
  simp_rw [hinner, integral_normSq_exp_half_g2]
  norm_num

lemma integral_V_H22 :
    ∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u = -1 := by
  rw [integral_fin4]
  have hm : MeasurableSet {pq : (ℝ × ℝ) × (ℝ × ℝ) | pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hint_prod : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2)) :=
    integrable_volume_mul_prod integrable_g2 integrable_normSq_g2
  have hint_ind : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) := by
    have heq : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) =
        {pq : (ℝ × ℝ) × (ℝ × ℝ) | pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2}.indicator
          (fun pq => g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2)) := by
      ext pq; simp [Set.indicator]
    rw [heq]
    exact hint_prod.indicator hm
  have hsplit : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 2 ^ 2 +
        (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 3 ^ 2) *
        H22 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2) -
        2 * ((if pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) := by
    ext pq
    unfold H22
    rw [gaussDensity_four_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    by_cases hcond : pq.1.1 ^ 2 + pq.1.2 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 <;> simp [hcond] <;> ring
  rw [hsplit, integral_sub hint_prod (hint_ind.const_mul 2), integral_const_mul,
    integral_volume_prod_mul g2 (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) * g2 q),
    integral_g2, integral_normSq_g2, one_mul,
    integral_volume_prod hint_ind]
  have hinner : ∀ p : ℝ × ℝ,
      (∫ q : ℝ × ℝ, (if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 p * ((q.1 ^ 2 + q.2 ^ 2) * g2 q))) =
      (p.1 ^ 2 + p.2 ^ 2) * exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p +
        2 * (exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) * g2 p) := by
    intro p
    have hf : (fun q : ℝ × ℝ => (if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 p * ((q.1 ^ 2 + q.2 ^ 2) * g2 q))) =
        fun q => g2 p * ((q.1 ^ 2 + q.2 ^ 2) *
          (if p.1 ^ 2 + p.2 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q) := by
      ext q; ring
    rw [hf, integral_const_mul, integral_tail_normSq_g2 (by positivity)]
    ring
  simp_rw [hinner]
  rw [integral_add integrable_normSq_exp_half_g2 (integrable_exp_half_g2.const_mul 2),
    integral_const_mul, integral_normSq_exp_half_g2, integral_exp_half_g2]
  norm_num

lemma integral_coord0_H22 : ∫ u : Fin 4 → ℝ, u 0 ^ 2 * H22 u * gaussDensity 4 u = 1 / 2 := by
  have hswap : (∫ u : Fin 4 → ℝ, u 1 ^ 2 * H22 u * gaussDensity 4 u) =
      ∫ u : Fin 4 → ℝ, u 0 ^ 2 * H22 u * gaussDensity 4 u := by
    rw [← integral_perm (Equiv.swap 0 1)]
    congr 1; ext u
    rw [gaussDensity_four_comp_perm]
    have hH : H22 (u ∘ Equiv.swap 0 1) = H22 u := by
      unfold H22
      simp [Equiv.swap_apply_def, add_comm]
    rw [hH]
    simp
  have hsum : (∫ u : Fin 4 → ℝ, (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 0 ^ 2 * H22 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 1 ^ 2 * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 0 ^ 2 * H22 u * gaussDensity 4 u + u 1 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 0 H22 measurable_H22 abs_H22_le)
      (integrable_coord_sq_witness_gauss 1 H22 measurable_H22 abs_H22_le)]
  linarith [integral_U_H22]

lemma integral_coord1_H22 : ∫ u : Fin 4 → ℝ, u 1 ^ 2 * H22 u * gaussDensity 4 u = 1 / 2 := by
  have hsum : (∫ u : Fin 4 → ℝ, (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 0 ^ 2 * H22 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 1 ^ 2 * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 0 ^ 2 * H22 u * gaussDensity 4 u + u 1 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 0 H22 measurable_H22 abs_H22_le)
      (integrable_coord_sq_witness_gauss 1 H22 measurable_H22 abs_H22_le)]
  linarith [integral_U_H22, integral_coord0_H22]

lemma integral_coord2_H22 : ∫ u : Fin 4 → ℝ, u 2 ^ 2 * H22 u * gaussDensity 4 u = -(1 / 2) := by
  have hswap : (∫ u : Fin 4 → ℝ, u 3 ^ 2 * H22 u * gaussDensity 4 u) =
      ∫ u : Fin 4 → ℝ, u 2 ^ 2 * H22 u * gaussDensity 4 u := by
    rw [← integral_perm (Equiv.swap 2 3)]
    congr 1; ext u
    rw [gaussDensity_four_comp_perm]
    have hH : H22 (u ∘ Equiv.swap 2 3) = H22 u := by
      unfold H22
      simp [Equiv.swap_apply_def, add_comm]
    rw [hH]
    simp
  have hsum : (∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 2 ^ 2 * H22 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 3 ^ 2 * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 2 ^ 2 * H22 u * gaussDensity 4 u + u 3 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 2 H22 measurable_H22 abs_H22_le)
      (integrable_coord_sq_witness_gauss 3 H22 measurable_H22 abs_H22_le)]
  linarith [integral_V_H22]

lemma integral_coord3_H22 : ∫ u : Fin 4 → ℝ, u 3 ^ 2 * H22 u * gaussDensity 4 u = -(1 / 2) := by
  have hsum : (∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 2 ^ 2 * H22 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 3 ^ 2 * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 2 ^ 2 * H22 u * gaussDensity 4 u + u 3 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 2 H22 measurable_H22 abs_H22_le)
      (integrable_coord_sq_witness_gauss 3 H22 measurable_H22 abs_H22_le)]
  linarith [integral_V_H22, integral_coord2_H22]

lemma case_2_2 (α : Fin 4 → ℝ) (h0 : 0 ≤ α 0) (h1 : 0 ≤ α 1) (h2 : α 2 ≤ 0) (h3 : α 3 ≤ 0) :
    (1 / 2 : ℝ) * (∑ i : Fin 4, |α i|) ≤ thetaIntegral 4 α := by
  have hw := thetaIntegral_ge_of_witness α H22 measurable_H22 abs_H22_le
  rw [Fin.sum_univ_four] at hw ⊢
  rw [integral_coord0_H22, integral_coord1_H22, integral_coord2_H22, integral_coord3_H22] at hw
  rw [abs_of_nonneg h0, abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonpos h3]
  linarith

noncomputable def alphaStar : Fin 4 → ℝ := ![1 / 4, 1 / 4, -(1 / 4), -(1 / 4)]

lemma alphaStar_norm_eq_one : ∑ i : Fin 4, |alphaStar i| = 1 := by
  rw [Fin.sum_univ_four]
  simp [alphaStar]
  norm_num

lemma thetaIntegral_alphaStar : thetaIntegral 4 alphaStar = 1 / 2 := by
  unfold thetaIntegral
  have hpt : (fun u : Fin 4 → ℝ => |∑ i : Fin 4, alphaStar i * u i ^ 2| * gaussDensity 4 u) =
      fun u => (1 / 4 : ℝ) * ((u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) -
        (1 / 4 : ℝ) * ((u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) := by
    ext u
    have hsum : (∑ i : Fin 4, alphaStar i * u i ^ 2) =
        (1 / 4 : ℝ) * ((u 0 ^ 2 + u 1 ^ 2) - (u 2 ^ 2 + u 3 ^ 2)) := by
      rw [Fin.sum_univ_four]
      simp [alphaStar]
      ring
    rw [hsum]
    unfold H22
    split_ifs with hle
    · rw [abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith)]
      ring
  have hintU : Integrable (fun u : Fin 4 → ℝ => (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 0 ^ 2 + u 1 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 0 ^ 2 * H22 u * gaussDensity 4 u + u 1 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf]
    exact (integrable_coord_sq_witness_gauss 0 H22 measurable_H22 abs_H22_le).add
      (integrable_coord_sq_witness_gauss 1 H22 measurable_H22 abs_H22_le)
  have hintV : Integrable (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * H22 u * gaussDensity 4 u) =
        fun u => u 2 ^ 2 * H22 u * gaussDensity 4 u + u 3 ^ 2 * H22 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf]
    exact (integrable_coord_sq_witness_gauss 2 H22 measurable_H22 abs_H22_le).add
      (integrable_coord_sq_witness_gauss 3 H22 measurable_H22 abs_H22_le)
  rw [hpt, integral_sub (hintU.const_mul _) (hintV.const_mul _),
    integral_const_mul, integral_const_mul, integral_U_H22, integral_V_H22]
  norm_num

/-! ### Case (1, 3) -/

noncomputable def h0 (u : Fin 4 → ℝ) : ℝ :=
  1 - 2 * (if (39 / 25 : ℝ) * u 0 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2 then (1 : ℝ) else 0)

def cycle123 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
def cycle123Sq : Equiv.Perm (Fin 4) := cycle123 * cycle123

noncomputable def H13 (u : Fin 4 → ℝ) : ℝ :=
  (h0 u + h0 (u ∘ cycle123) + h0 (u ∘ cycle123Sq)) / 3

lemma measurable_comp_perm (τ : Equiv.Perm (Fin 4)) :
    Measurable (fun u : Fin 4 → ℝ => u ∘ τ) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (τ i)

lemma measurable_h0 : Measurable h0 := by
  have hm : MeasurableSet {u : Fin 4 → ℝ | (39 / 25 : ℝ) * u 0 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have h : (fun u : Fin 4 → ℝ => if (39 / 25 : ℝ) * u 0 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2 then (1 : ℝ) else 0) =
      {u : Fin 4 → ℝ | (39 / 25 : ℝ) * u 0 ^ 2 ≤ u 2 ^ 2 + u 3 ^ 2}.indicator (fun _ => 1) := by
    ext u; simp [Set.indicator]
  unfold h0
  exact measurable_const.sub (measurable_const.mul (h ▸ measurable_const.indicator hm))

lemma abs_h0_le (u : Fin 4 → ℝ) : |h0 u| ≤ 1 := by
  unfold h0
  split_ifs <;> norm_num

lemma measurable_H13 : Measurable H13 := by
  unfold H13
  have hm1 : Measurable (fun u : Fin 4 → ℝ => h0 (u ∘ cycle123)) :=
    measurable_h0.comp (measurable_comp_perm cycle123)
  have hm2 : Measurable (fun u : Fin 4 → ℝ => h0 (u ∘ cycle123Sq)) :=
    measurable_h0.comp (measurable_comp_perm cycle123Sq)
  exact ((measurable_h0.add hm1).add hm2).div_const 3

lemma abs_H13_le (u : Fin 4 → ℝ) : |H13 u| ≤ 1 := by
  unfold H13
  have b0 := abs_h0_le u
  have b1 := abs_h0_le (u ∘ cycle123)
  have b2 := abs_h0_le (u ∘ cycle123Sq)
  rw [abs_le] at b0 b1 b2 ⊢
  constructor <;> linarith

lemma integral_coord0_h0 :
    ∫ u : Fin 4 → ℝ, u 0 ^ 2 * h0 u * gaussDensity 4 u = 131 / 256 := by
  rw [integral_fin4]
  have hm : MeasurableSet {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hint_prod : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2) :=
    integrable_volume_mul_prod integrable_fst_sq_g2 integrable_g2
  have hint_ind : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
        ((pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2)) := by
    have heq : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          ((pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2)) =
        {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2}.indicator
          (fun pq => (pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2) := by
      ext pq; simp [Set.indicator]
    rw [heq]
    exact hint_prod.indicator hm
  have hsplit : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 0 ^ 2 *
        h0 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => (pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2 -
        2 * ((if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          ((pq.1.1 ^ 2 * g2 pq.1) * g2 pq.2)) := by
    ext pq
    unfold h0
    rw [gaussDensity_four_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val]
    by_cases hcond : (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 <;> simp [hcond] <;> ring
  rw [hsplit, integral_sub hint_prod (hint_ind.const_mul 2), integral_const_mul,
    integral_volume_prod_mul (fun p : ℝ × ℝ => p.1 ^ 2 * g2 p) g2,
    integral_fst_sq_g2, integral_g2, mul_one,
    integral_volume_prod hint_ind]
  have hinner : ∀ p : ℝ × ℝ,
      (∫ q : ℝ × ℝ, (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        ((p.1 ^ 2 * g2 p) * g2 q)) =
      (p.1 ^ 2 * exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * g1 p.2 := by
    intro p
    have hf : (fun q : ℝ × ℝ => (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        ((p.1 ^ 2 * g2 p) * g2 q)) =
        fun q => (p.1 ^ 2 * g2 p) *
          ((if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q) := by
      ext q; ring
    rw [hf, integral_const_mul, integral_tail_g2 (by positivity)]
    unfold g2
    have he : -((39 / 25 : ℝ) * p.1 ^ 2) / 2 = -(39 / 50 : ℝ) * p.1 ^ 2 := by ring
    rw [he]; ring
  simp_rw [hinner]
  rw [integral_volume_prod_mul (fun x => x ^ 2 * exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x) g1,
    integral_sq_mul_exp_39_50_mul_g1, integral_g1, mul_one]
  norm_num

lemma integral_coord1_h0 :
    ∫ u : Fin 4 → ℝ, u 1 ^ 2 * h0 u * gaussDensity 4 u = -(1 / 4) := by
  rw [integral_fin4]
  have hm : MeasurableSet {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hint_prod : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2) :=
    integrable_volume_mul_prod integrable_snd_sq_g2 integrable_g2
  have hint_ind : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
        ((pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2)) := by
    have heq : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          ((pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2)) =
        {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2}.indicator
          (fun pq => (pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2) := by
      ext pq; simp [Set.indicator]
    rw [heq]
    exact hint_prod.indicator hm
  have hsplit : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 1 ^ 2 *
        h0 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => (pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2 -
        2 * ((if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          ((pq.1.2 ^ 2 * g2 pq.1) * g2 pq.2)) := by
    ext pq
    unfold h0
    rw [gaussDensity_four_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    by_cases hcond : (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 <;> simp [hcond] <;> ring
  rw [hsplit, integral_sub hint_prod (hint_ind.const_mul 2), integral_const_mul,
    integral_volume_prod_mul (fun p : ℝ × ℝ => p.2 ^ 2 * g2 p) g2,
    integral_snd_sq_g2, integral_g2, mul_one,
    integral_volume_prod hint_ind]
  have hinner : ∀ p : ℝ × ℝ,
      (∫ q : ℝ × ℝ, (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        ((p.2 ^ 2 * g2 p) * g2 q)) =
      (exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * (p.2 ^ 2 * g1 p.2) := by
    intro p
    have hf : (fun q : ℝ × ℝ => (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        ((p.2 ^ 2 * g2 p) * g2 q)) =
        fun q => (p.2 ^ 2 * g2 p) *
          ((if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q) := by
      ext q; ring
    rw [hf, integral_const_mul, integral_tail_g2 (by positivity)]
    unfold g2
    have he : -((39 / 25 : ℝ) * p.1 ^ 2) / 2 = -(39 / 50 : ℝ) * p.1 ^ 2 := by ring
    rw [he]; ring
  simp_rw [hinner]
  rw [integral_volume_prod_mul (fun x => exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x)
    (fun x => x ^ 2 * g1 x),
    integral_exp_39_50_mul_g1, integral_sq_mul_g1, mul_one]
  norm_num

lemma integral_coord23_h0 :
    ∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * h0 u * gaussDensity 4 u = -323 / 256 := by
  rw [integral_fin4]
  have hm : MeasurableSet {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hint_prod : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2)) :=
    integrable_volume_mul_prod integrable_g2 integrable_normSq_g2
  have hint_ind : Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) := by
    have heq : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
        (if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) =
        {pq : (ℝ × ℝ) × (ℝ × ℝ) | (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2}.indicator
          (fun pq => g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2)) := by
      ext pq; simp [Set.indicator]
    rw [heq]
    exact hint_prod.indicator hm
  have hsplit : (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      ((![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 2 ^ 2 +
        (![pq.1.1, pq.1.2, pq.2.1, pq.2.2] : Fin 4 → ℝ) 3 ^ 2) *
        h0 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2] *
        gaussDensity 4 ![pq.1.1, pq.1.2, pq.2.1, pq.2.2]) =
      fun pq => g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2) -
        2 * ((if (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 then (1 : ℝ) else 0) *
          (g2 pq.1 * ((pq.2.1 ^ 2 + pq.2.2 ^ 2) * g2 pq.2))) := by
    ext pq
    unfold h0
    rw [gaussDensity_four_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val]
    by_cases hcond : (39 / 25 : ℝ) * pq.1.1 ^ 2 ≤ pq.2.1 ^ 2 + pq.2.2 ^ 2 <;> simp [hcond] <;> ring
  rw [hsplit, integral_sub hint_prod (hint_ind.const_mul 2), integral_const_mul,
    integral_volume_prod_mul g2 (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) * g2 q),
    integral_g2, integral_normSq_g2, one_mul,
    integral_volume_prod hint_ind]
  have hinner : ∀ p : ℝ × ℝ,
      (∫ q : ℝ × ℝ, (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 p * ((q.1 ^ 2 + q.2 ^ 2) * g2 q))) =
      (39 / 25 : ℝ) * ((p.1 ^ 2 * exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * g1 p.2) +
        2 * ((exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * g1 p.2) := by
    intro p
    have hf : (fun q : ℝ × ℝ => (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) *
        (g2 p * ((q.1 ^ 2 + q.2 ^ 2) * g2 q))) =
        fun q => g2 p * ((q.1 ^ 2 + q.2 ^ 2) *
          (if (39 / 25 : ℝ) * p.1 ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 then (1 : ℝ) else 0) * g2 q) := by
      ext q; ring
    rw [hf, integral_const_mul, integral_tail_normSq_g2 (by positivity)]
    unfold g2
    have he : -((39 / 25 : ℝ) * p.1 ^ 2) / 2 = -(39 / 50 : ℝ) * p.1 ^ 2 := by ring
    rw [he]; ring
  simp_rw [hinner]
  have hintA : Integrable (fun p : ℝ × ℝ => (p.1 ^ 2 * exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * g1 p.2) := by
    refine integrable_fst_sq_g2.mono' (by unfold g1; exact Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with p
    have hg1 : 0 ≤ g1 p.1 := g1_nonneg p.1
    have hg2 : 0 ≤ g1 p.2 := g1_nonneg p.2
    have hle : exp (-(39 / 50 : ℝ) * p.1 ^ 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold g2
    calc
      p.1 ^ 2 * exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1 * g1 p.2 =
          exp (-(39 / 50 : ℝ) * p.1 ^ 2) * (p.1 ^ 2 * (g1 p.1 * g1 p.2)) := by ring
      _ ≤ 1 * (p.1 ^ 2 * (g1 p.1 * g1 p.2)) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = p.1 ^ 2 * (g1 p.1 * g1 p.2) := one_mul _
  have hintB : Integrable (fun p : ℝ × ℝ => (exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1) * g1 p.2) := by
    refine integrable_g2.mono' (by unfold g1; exact Continuous.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards with p
    have hg1 : 0 ≤ g1 p.1 := g1_nonneg p.1
    have hg2 : 0 ≤ g1 p.2 := g1_nonneg p.2
    have hle : exp (-(39 / 50 : ℝ) * p.1 ^ 2) ≤ 1 :=
      exp_le_one_iff.mpr (by nlinarith [sq_nonneg p.1])
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold g2
    calc
      exp (-(39 / 50 : ℝ) * p.1 ^ 2) * g1 p.1 * g1 p.2 =
          exp (-(39 / 50 : ℝ) * p.1 ^ 2) * (g1 p.1 * g1 p.2) := by ring
      _ ≤ 1 * (g1 p.1 * g1 p.2) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = g1 p.1 * g1 p.2 := one_mul _
  rw [integral_add (hintA.const_mul _) (hintB.const_mul _), integral_const_mul, integral_const_mul,
    integral_volume_prod_mul (fun x => x ^ 2 * exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x) g1,
    integral_volume_prod_mul (fun x => exp (-(39 / 50 : ℝ) * x ^ 2) * g1 x) g1,
    integral_sq_mul_exp_39_50_mul_g1, integral_exp_39_50_mul_g1, integral_g1]
  norm_num

lemma integral_coord2_h0 :
    ∫ u : Fin 4 → ℝ, u 2 ^ 2 * h0 u * gaussDensity 4 u = -323 / 512 := by
  have hswap : (∫ u : Fin 4 → ℝ, u 3 ^ 2 * h0 u * gaussDensity 4 u) =
      ∫ u : Fin 4 → ℝ, u 2 ^ 2 * h0 u * gaussDensity 4 u := by
    rw [← integral_perm (Equiv.swap 2 3)]
    congr 1; ext u
    rw [gaussDensity_four_comp_perm]
    have hh : h0 (u ∘ Equiv.swap 2 3) = h0 u := by
      unfold h0
      simp [Equiv.swap_apply_def, add_comm]
    rw [hh]
    simp
  have hsum : (∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * h0 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 2 ^ 2 * h0 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 3 ^ 2 * h0 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * h0 u * gaussDensity 4 u) =
        fun u => u 2 ^ 2 * h0 u * gaussDensity 4 u + u 3 ^ 2 * h0 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 2 h0 measurable_h0 abs_h0_le)
      (integrable_coord_sq_witness_gauss 3 h0 measurable_h0 abs_h0_le)]
  linarith [integral_coord23_h0]

lemma integral_coord3_h0 :
    ∫ u : Fin 4 → ℝ, u 3 ^ 2 * h0 u * gaussDensity 4 u = -323 / 512 := by
  have hsum : (∫ u : Fin 4 → ℝ, (u 2 ^ 2 + u 3 ^ 2) * h0 u * gaussDensity 4 u) =
      (∫ u : Fin 4 → ℝ, u 2 ^ 2 * h0 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u 3 ^ 2 * h0 u * gaussDensity 4 u) := by
    have hf : (fun u : Fin 4 → ℝ => (u 2 ^ 2 + u 3 ^ 2) * h0 u * gaussDensity 4 u) =
        fun u => u 2 ^ 2 * h0 u * gaussDensity 4 u + u 3 ^ 2 * h0 u * gaussDensity 4 u := by
      ext u; ring
    rw [hf, integral_add
      (integrable_coord_sq_witness_gauss 2 h0 measurable_h0 abs_h0_le)
      (integrable_coord_sq_witness_gauss 3 h0 measurable_h0 abs_h0_le)]
  linarith [integral_coord23_h0, integral_coord2_h0]

lemma integral_h0_perm (τ : Equiv.Perm (Fin 4)) (m : Fin 4) :
    (∫ u : Fin 4 → ℝ, u m ^ 2 * h0 (u ∘ τ) * gaussDensity 4 u) =
      ∫ u : Fin 4 → ℝ, u (τ⁻¹ m) ^ 2 * h0 u * gaussDensity 4 u := by
  rw [← integral_perm τ⁻¹]
  congr 1; ext u
  rw [gaussDensity_four_comp_perm]
  have hcomp : (u ∘ ⇑τ⁻¹) ∘ ⇑τ = u := by
    ext i; simp
  rw [hcomp]
  rfl

lemma integral_coord_H13_expand (m : Fin 4) :
    (∫ u : Fin 4 → ℝ, u m ^ 2 * H13 u * gaussDensity 4 u) =
      ((∫ u : Fin 4 → ℝ, u m ^ 2 * h0 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u (cycle123⁻¹ m) ^ 2 * h0 u * gaussDensity 4 u) +
        (∫ u : Fin 4 → ℝ, u (cycle123Sq⁻¹ m) ^ 2 * h0 u * gaussDensity 4 u)) / 3 := by
  have hm1 : Measurable (fun u : Fin 4 → ℝ => h0 (u ∘ cycle123)) :=
    measurable_h0.comp (measurable_comp_perm cycle123)
  have hm2 : Measurable (fun u : Fin 4 → ℝ => h0 (u ∘ cycle123Sq)) :=
    measurable_h0.comp (measurable_comp_perm cycle123Sq)
  have i0 := integrable_coord_sq_witness_gauss m h0 measurable_h0 abs_h0_le
  have i1 := integrable_coord_sq_witness_gauss m (fun u => h0 (u ∘ cycle123)) hm1
    (fun u => abs_h0_le _)
  have i2 := integrable_coord_sq_witness_gauss m (fun u => h0 (u ∘ cycle123Sq)) hm2
    (fun u => abs_h0_le _)
  have i01 : Integrable (fun u : Fin 4 → ℝ =>
      u m ^ 2 * h0 u * gaussDensity 4 u + u m ^ 2 * h0 (u ∘ cycle123) * gaussDensity 4 u) :=
    i0.add i1
  have hsplit : (fun u : Fin 4 → ℝ => u m ^ 2 * H13 u * gaussDensity 4 u) =
      fun u => ((u m ^ 2 * h0 u * gaussDensity 4 u +
        u m ^ 2 * h0 (u ∘ cycle123) * gaussDensity 4 u) +
        u m ^ 2 * h0 (u ∘ cycle123Sq) * gaussDensity 4 u) / 3 := by
    ext u; unfold H13; ring
  rw [hsplit, integral_div, integral_add i01 i2, integral_add i0 i1,
    integral_h0_perm cycle123 m, integral_h0_perm cycle123Sq m]

lemma integral_coord0_H13 :
    ∫ u : Fin 4 → ℝ, u 0 ^ 2 * H13 u * gaussDensity 4 u = 131 / 256 := by
  rw [integral_coord_H13_expand 0]
  have hc1 : cycle123⁻¹ 0 = 0 := by decide
  have hc2 : cycle123Sq⁻¹ 0 = 0 := by decide
  rw [hc1, hc2, integral_coord0_h0]
  norm_num

lemma integral_coord1_H13 :
    ∫ u : Fin 4 → ℝ, u 1 ^ 2 * H13 u * gaussDensity 4 u = -129 / 256 := by
  rw [integral_coord_H13_expand 1]
  have hc1 : cycle123⁻¹ 1 = 3 := by decide
  have hc2 : cycle123Sq⁻¹ 1 = 2 := by decide
  rw [hc1, hc2, integral_coord1_h0, integral_coord3_h0, integral_coord2_h0]
  norm_num

lemma integral_coord2_H13 :
    ∫ u : Fin 4 → ℝ, u 2 ^ 2 * H13 u * gaussDensity 4 u = -129 / 256 := by
  rw [integral_coord_H13_expand 2]
  have hc1 : cycle123⁻¹ 2 = 1 := by decide
  have hc2 : cycle123Sq⁻¹ 2 = 3 := by decide
  rw [hc1, hc2, integral_coord2_h0, integral_coord1_h0, integral_coord3_h0]
  norm_num

lemma integral_coord3_H13 :
    ∫ u : Fin 4 → ℝ, u 3 ^ 2 * H13 u * gaussDensity 4 u = -129 / 256 := by
  rw [integral_coord_H13_expand 3]
  have hc1 : cycle123⁻¹ 3 = 2 := by decide
  have hc2 : cycle123Sq⁻¹ 3 = 1 := by decide
  rw [hc1, hc2, integral_coord3_h0, integral_coord2_h0, integral_coord1_h0]
  norm_num

lemma case_1_3 (α : Fin 4 → ℝ) (h0p : 0 ≤ α 0) (h1n : α 1 ≤ 0) (h2n : α 2 ≤ 0) (h3n : α 3 ≤ 0) :
    (1 / 2 : ℝ) * (∑ i : Fin 4, |α i|) ≤ thetaIntegral 4 α := by
  have hw := thetaIntegral_ge_of_witness α H13 measurable_H13 abs_H13_le
  rw [Fin.sum_univ_four] at hw ⊢
  rw [integral_coord0_H13, integral_coord1_H13, integral_coord2_H13, integral_coord3_H13] at hw
  rw [abs_of_nonneg h0p, abs_of_nonpos h1n, abs_of_nonpos h2n, abs_of_nonpos h3n]
  linarith

/-! ### Symmetry Reduction Across All Sign Configurations -/

lemma sum_abs_neg (α : Fin 4 → ℝ) : (∑ i : Fin 4, |(-α) i|) = ∑ i : Fin 4, |α i| := by
  simp [Pi.neg_apply]

lemma sum_abs_perm (σ : Equiv.Perm (Fin 4)) (α : Fin 4 → ℝ) :
    (∑ i : Fin 4, |(α ∘ σ) i|) = ∑ i : Fin 4, |α i| :=
  Equiv.sum_comp σ (fun i => |α i|)

lemma half_sum_abs_le_thetaIntegral (α : Fin 4 → ℝ) :
    (1 / 2 : ℝ) * (∑ i : Fin 4, |α i|) ≤ thetaIntegral 4 α := by
  have neg_red : ∀ β : Fin 4 → ℝ,
      (1 / 2 : ℝ) * (∑ i : Fin 4, |(-β) i|) ≤ thetaIntegral 4 (-β) →
      (1 / 2 : ℝ) * (∑ i : Fin 4, |β i|) ≤ thetaIntegral 4 β := by
    intro β h
    rwa [sum_abs_neg, thetaIntegral_neg] at h
  have perm_red : ∀ (σ : Equiv.Perm (Fin 4)) (β : Fin 4 → ℝ),
      (1 / 2 : ℝ) * (∑ i : Fin 4, |(β ∘ σ) i|) ≤ thetaIntegral 4 (β ∘ σ) →
      (1 / 2 : ℝ) * (∑ i : Fin 4, |β i|) ≤ thetaIntegral 4 β := by
    intro σ β h
    rwa [sum_abs_perm, thetaIntegral_perm] at h
  rcases le_total 0 (α 0) with s0 | s0 <;>
    rcases le_total 0 (α 1) with s1 | s1 <;>
    rcases le_total 0 (α 2) with s2 | s2 <;>
    rcases le_total 0 (α 3) with s3 | s3
  · exact case_4_0 α s0 s1 s2 s3
  · refine neg_red α (perm_red (Equiv.swap 0 3) (-α) ?_)
    exact case_1_3 ((-α) ∘ Equiv.swap 0 3)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine neg_red α (perm_red (Equiv.swap 0 2) (-α) ?_)
    exact case_1_3 ((-α) ∘ Equiv.swap 0 2)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · exact case_2_2 α s0 s1 s2 s3
  · refine neg_red α (perm_red (Equiv.swap 0 1) (-α) ?_)
    exact case_1_3 ((-α) ∘ Equiv.swap 0 1)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine perm_red (Equiv.swap 1 2) α ?_
    exact case_2_2 (α ∘ Equiv.swap 1 2)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine perm_red (Equiv.swap 1 3) α ?_
    exact case_2_2 (α ∘ Equiv.swap 1 3)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · exact case_1_3 α s0 s1 s2 s3
  · refine neg_red α ?_
    exact case_1_3 (-α) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)
  · refine perm_red (Equiv.swap 0 2) α ?_
    exact case_2_2 (α ∘ Equiv.swap 0 2)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine perm_red (Equiv.swap 0 3) α ?_
    exact case_2_2 (α ∘ Equiv.swap 0 3)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine perm_red (Equiv.swap 0 1) α ?_
    exact case_1_3 (α ∘ Equiv.swap 0 1)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine neg_red α ?_
    exact case_2_2 (-α) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)
  · refine perm_red (Equiv.swap 0 2) α ?_
    exact case_1_3 (α ∘ Equiv.swap 0 2)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine perm_red (Equiv.swap 0 3) α ?_
    exact case_1_3 (α ∘ Equiv.swap 0 3)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
      (by rw [Function.comp_apply, Equiv.swap_apply_def]; simp; linarith)
  · refine neg_red α ?_
    exact case_4_0 (-α) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)

end RobustOpt2009ThetaFourAux

open RobustOpt2009ThetaFourAux in
theorem solution : ModernConvex.MatrixCube.theta 4 = 2 := by
  have hisLeast : IsLeast
      (ModernConvex.MatrixCube.thetaIntegral 4 '' {α : Fin 4 → ℝ | ∑ i : Fin 4, |α i| = 1})
      (1 / 2 : ℝ) := by
    refine ⟨⟨alphaStar, alphaStar_norm_eq_one, thetaIntegral_alphaStar⟩, ?_⟩
    rintro _ ⟨α, hα, rfl⟩
    have h := half_sum_abs_le_thetaIntegral α
    rw [hα, mul_one] at h
    exact h
  unfold ModernConvex.MatrixCube.theta
  rw [hisLeast.csInf_eq]
  norm_num
