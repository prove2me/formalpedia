-- Prove2me | solution 1 for Roberts1997.RWM.gaussian_increment_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:19:10.425806+00:00
-- url     : https://prove2.me/submissions/d774657d-277e-43a4-a7c8-d22dbb003dd9

import Definitions.Def_Roberts1997_RWM_Target

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

namespace Roberts1997.RWM

theorem aux_gib_taylor (V : ℝ → ℝ) (hd : Differentiable ℝ V) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ a b, |deriv V a - deriv V b| ≤ K * |a - b|) (x y : ℝ) :
    |V y - V x - deriv V x * (y - x)| ≤ K * (y - x) ^ 2 := by
  set g : ℝ → ℝ := fun z => V z - deriv V x * z with hg
  have hgd : ∀ z, HasDerivAt g (deriv V z - deriv V x) z := by
    intro z
    have h2 : HasDerivAt (fun y => deriv V x * y) (deriv V x) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv V x)
    exact ((hd z).hasDerivAt).sub h2
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.uIcc x y)
    (C := K * |y - x|)
    (fun z _ => (hgd z).differentiableAt)
    (fun z hz => by
      rw [(hgd z).deriv, Real.norm_eq_abs]
      refine (hK z x).trans ?_
      exact mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hz) hK0)
    (convex_uIcc x y) Set.left_mem_uIcc Set.right_mem_uIcc
  have hgyx : g y - g x = V y - V x - deriv V x * (y - x) := by
    simp only [g]; ring
  rw [hgyx, Real.norm_eq_abs, Real.norm_eq_abs] at key
  calc |V y - V x - deriv V x * (y - x)| ≤ K * |y - x| * |y - x| := key
    _ = K * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

theorem aux_gib_int (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) (K : ℝ)
    (hK0 : 0 ≤ K) (hK : ∀ a b, |deriv V a - deriv V b| ≤ K * |a - b|) (x : ℝ) (v : NNReal) :
    |∫ y, (V y - V x) ∂(gaussianReal x v)| ≤ K * v := by
  set μ := gaussianReal x v with hμ
  have hd : Differentiable ℝ V := hV.differentiable (by simp)
  have hVi : Integrable V μ := hV.continuous.integrable_of_hasCompactSupport hVc
  have hidi : Integrable (fun y => y) μ :=
    (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
  have hlin : Integrable (fun y => deriv V x * (y - x)) μ :=
    (hidi.sub (integrable_const x)).const_mul _
  have hsq : Integrable (fun y => (y - x) ^ 2) μ :=
    ((memLp_id_gaussianReal' 2 (by simp)).sub (memLp_const x)).integrable_sq
  have hmean : ∫ y, y ∂μ = x := integral_id_gaussianReal
  have hvar : ∫ y, (y - x) ^ 2 ∂μ = v := by
    have := variance_eq_integral (X := id) (μ := μ) measurable_id.aemeasurable
    rw [variance_id_gaussianReal] at this
    simp only [id] at this
    rw [hmean] at this
    exact this.symm
  have hsplit : ∫ y, (V y - V x) ∂μ = ∫ y, (V y - V x - deriv V x * (y - x)) ∂μ := by
    have h1 : ∫ y, deriv V x * (y - x) ∂μ = 0 := by
      rw [integral_const_mul, integral_sub hidi (integrable_const x), hmean]; simp
    have hA : Integrable (fun y => V y - V x) μ := hVi.sub (integrable_const _)
    rw [integral_sub hA hlin, h1, sub_zero]
  rw [hsplit]
  calc |∫ y, (V y - V x - deriv V x * (y - x)) ∂μ| ≤ ∫ y, K * (y - x) ^ 2 ∂μ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hsq.const_mul K) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs]; exact aux_gib_taylor V hd K hK0 hK x y
    _ = K * v := by rw [integral_const_mul, hvar]

end Roberts1997.RWM

open Roberts1997.RWM

theorem solution (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (l : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ x₁ : ℝ,
      (n : ℝ) * |∫ y, (V y - V x₁) ∂(gaussianReal x₁ (sigmaSq n l).toNNReal)| ≤ C := by
  have hV' : ContDiff ℝ ∞ (deriv V) := (contDiff_infty_iff_deriv.mp hV).2
  obtain ⟨L, hL⟩ := hV'.lipschitzWith_of_hasCompactSupport hVc.deriv (by simp)
  set K : ℝ := (L : ℝ) with hKdef
  have hK0 : 0 ≤ K := L.2
  have hK : ∀ a b, |deriv V a - deriv V b| ≤ K * |a - b| := by
    intro a b
    have := hL.dist_le_mul a b
    simpa [Real.dist_eq] using this
  refine ⟨2 * K * l ^ 2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn x₁
  have hb := aux_gib_int V hV hVc K hK0 hK x₁ (sigmaSq n l).toNNReal
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hpos : 0 ≤ sigmaSq n l := by unfold sigmaSq; positivity
  rw [Real.coe_toNNReal _ hpos] at hb
  have hs : (n : ℝ) * sigmaSq n l ≤ 2 * l ^ 2 := by
    unfold sigmaSq
    rw [mul_div_assoc', div_le_iff₀ hn1]
    nlinarith [mul_nonneg (sq_nonneg l) (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2)]
  calc (n : ℝ) * |∫ y, (V y - V x₁) ∂(gaussianReal x₁ (sigmaSq n l).toNNReal)|
      ≤ (n : ℝ) * (K * sigmaSq n l) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = K * ((n : ℝ) * sigmaSq n l) := by ring
    _ ≤ K * (2 * l ^ 2) := mul_le_mul_of_nonneg_left hs hK0
    _ = 2 * K * l ^ 2 := by ring
