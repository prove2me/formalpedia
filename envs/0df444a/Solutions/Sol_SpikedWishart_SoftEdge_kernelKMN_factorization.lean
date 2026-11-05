-- Prove2me | solution 1 for SpikedWishart.SoftEdge.kernelKMN_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:19:08.005855+00:00
-- url     : https://prove2.me/submissions/8f5bcecf-261a-4ef9-a15f-a48a616fd928

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Kernels

set_option autoImplicit false

namespace Lib5e

open MeasureTheory Filter Topology Set Complex

/-- R6a. `1/(w-z) = -σ ∫₀^∞ e^{σ y (w - z)} dy` when `Re(w - z) < 0`, `σ > 0`. -/
theorem inv_sub_eq_neg_integral (w z : ℂ) (σ : ℝ) (hσ : 0 < σ) (h : (w - z).re < 0) :
    1 / (w - z) = -(σ : ℂ) * ∫ y in Ioi (0 : ℝ), exp (((σ * y : ℝ) : ℂ) * (w - z)) := by
  have ha : ((σ : ℂ) * (w - z)).re < 0 := by
    rw [Complex.re_ofReal_mul]; exact mul_neg_of_pos_of_neg hσ h
  have hint := integral_exp_mul_complex_Ioi ha 0
  have hcongr : (fun y : ℝ => exp (((σ * y : ℝ) : ℂ) * (w - z))) =
      fun y : ℝ => exp ((σ : ℂ) * (w - z) * y) := by
    funext y; congr 1; push_cast; ring
  rw [hcongr, hint]
  have hwz : w - z ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  simp only [ofReal_zero, mul_zero, exp_zero]
  field_simp

/-- Fubini swap of `∫₀^{2π} dθ` and `∫₀^∞ dy` for a continuous, exponentially decaying integrand. -/
theorem swap_interval_Ioi (F : ℝ → ℝ → ℂ) (hF : Continuous (Function.uncurry F)) (K δ : ℝ)
    (hδ : 0 < δ) (hb : ∀ θ y : ℝ, 0 < y → ‖F θ y‖ ≤ K * Real.exp (-δ * y)) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ y in Ioi (0 : ℝ), F θ y =
      ∫ y in Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..2 * Real.pi, F θ y := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h2π]
  simp_rw [intervalIntegral.integral_of_le h2π]
  refine integral_integral_swap ?_
  have hS : MeasurableSet (Ioc (0 : ℝ) (2 * Real.pi) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioc.prod measurableSet_Ioi
  have hg : Integrable (fun p : ℝ × ℝ => (fun _ : ℝ => K) p.1 * (fun y : ℝ => Real.exp (-δ * y)) p.2)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod (integrable_const K) (integrableOn_exp_mul_Ioi (by linarith) 0)
  refine hg.mono' hF.aestronglyMeasurable ?_
  rw [Measure.prod_restrict, ae_restrict_iff' hS]
  exact Filter.Eventually.of_forall (fun p hp => hb p.1 p.2 hp.2)

/-- R6b. `e^{M f(z)} = e^{-Mµ(z-q)} z^M / (1-z)^N` when `γ² = M/N`. -/
theorem exp_M_fFn (γ q : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hγ : γ ^ 2 = (M : ℝ) / N)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    exp ((M : ℂ) * SpikedWishart.SoftEdge.fFn γ q z) =
      exp (-(M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q)) * z ^ M / (1 - z) ^ N := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hγc : (γ : ℂ) ^ 2 = (((M : ℝ) / N : ℝ) : ℂ) := by rw [← hγ]; push_cast; ring
  have hMN : (M : ℂ) * (1 / (γ : ℂ) ^ 2) = N := by
    rw [hγc]; push_cast; field_simp
  unfold SpikedWishart.SoftEdge.fFn
  have e : (M : ℂ) * (-(SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q) + log z -
      (1 / (γ : ℂ) ^ 2) * log (1 - z)) =
      -(M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q) + M * log z - N * log (1 - z) := by
    rw [← hMN]; ring
  rw [e, exp_sub, exp_add, exp_nat_mul, exp_nat_mul, exp_log hz0, exp_log hz1]

theorem exp_neg_M_fFn (γ q : ℝ) (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (hγ : γ ^ 2 = (M : ℝ) / N)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0) :
    exp (-(M : ℂ) * SpikedWishart.SoftEdge.fFn γ q z) =
      exp ((M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q)) * (1 - z) ^ N / z ^ M := by
  rw [neg_mul, exp_neg, exp_M_fFn γ q M N hM hN hγ z hz0 hz1]
  have hE : exp (-(M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q)) =
      (exp ((M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q)))⁻¹ := by
    rw [← exp_neg]; ring_nf
  have h2 : exp ((M : ℂ) * (SpikedWishart.SoftEdge.mu γ : ℂ) * (z - q)) ≠ 0 := exp_ne_zero _
  have h3 : z ^ M ≠ 0 := pow_ne_zero _ hz0
  have h4 : (1 - z) ^ N ≠ 0 := pow_ne_zero _ hz1
  rw [hE, inv_div]
  field_simp

/-- R6c. Split `∏_{j<N} (π_j - w)` when `π_j = 1` for `j ≥ r`. -/
theorem prod_split {N r : ℕ} (hr : r ≤ N) (π : Fin N → ℝ) (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1)
    (w : ℂ) :
    ∏ j, ((π j : ℂ) - w) =
      (∏ j : Fin r, ((π ⟨j, lt_of_lt_of_le j.2 hr⟩ : ℂ) - w)) * (1 - w) ^ (N - r) := by
  let f : ℕ → ℂ := fun i => if h : i < N then (π ⟨i, h⟩ : ℂ) - w else 1
  have e1 : ∏ j : Fin N, ((π j : ℂ) - w) = ∏ i ∈ Finset.range N, f i := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [f, j.2]
  have e2 : ∏ j : Fin r, ((π ⟨j, lt_of_lt_of_le j.2 hr⟩ : ℂ) - w) = ∏ i ∈ Finset.range r, f i := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp [f, lt_of_lt_of_le j.2 hr]
  have e3 : ∏ i ∈ Finset.Ico r N, f i = (1 - w) ^ (N - r) := by
    rw [← Nat.card_Ico r N, ← Finset.prod_const]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ico] at hi
    simp only [f, dif_pos hi.2]
    rw [h1 ⟨i, hi.2⟩ hi.1]
    simp
  rw [e1, e2, ← e3, Finset.prod_range_mul_prod_Ico f hr]


theorem deriv_circleMap_fun (c : ℂ) (R : ℝ) :
    (fun θ : ℝ => deriv (circleMap c R) θ) = fun θ => circleMap 0 R θ * I :=
  funext (deriv_circleMap c R)

theorem norm_deriv_circleMap' (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (θ : ℝ) :
    ‖deriv (circleMap c R) θ‖ = R := by
  rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one, abs_of_nonneg hR]

theorem norm_exp_real_mul (t : ℝ) (w : ℂ) : ‖exp (((t : ℝ) : ℂ) * w)‖ = Real.exp (t * w.re) := by
  rw [norm_exp, Complex.re_ofReal_mul]

/-- R6d-1. The parametric circle integral `y ↦ ∮ e^{σ y w} b(w) dw` is continuous and grows at
most like `e^{σ Y y}` when `Re w ≤ Y` on the circle. -/
theorem circle_exp_cont_bound (b : ℂ → ℂ) (c : ℂ) (R σ Y : ℝ) (hR : 0 ≤ R) (hσ : 0 < σ)
    (hb : ContinuousOn b (Metric.sphere c R)) (hY : ∀ w ∈ Metric.sphere c R, w.re ≤ Y) :
    Continuous (fun y : ℝ => ∮ w in C(c, R), exp (((σ * y : ℝ) : ℂ) * w) * b w) ∧
      ∃ CB : ℝ, ∀ y : ℝ, 0 < y → ‖∮ w in C(c, R), exp (((σ * y : ℝ) : ℂ) * w) * b w‖ ≤
        CB * Real.exp (σ * Y * y) := by
  obtain ⟨Cb, hCb⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hb
  have hbc : Continuous (fun φ : ℝ => b (circleMap c R φ)) :=
    hb.comp_continuous (continuous_circleMap c R) (fun φ => circleMap_mem_sphere c hR φ)
  constructor
  · unfold circleIntegral
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * Real.pi)
    have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap c R) p.2 := by
      simp only [deriv_circleMap]; exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    have h3 : Continuous fun p : ℝ × ℝ => exp (((σ * p.1 : ℝ) : ℂ) * circleMap c R p.2) :=
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst)).mul
        ((continuous_circleMap c R).comp continuous_snd)).cexp
    exact h1.smul (h3.mul (hbc.comp continuous_snd))
  · refine ⟨2 * Real.pi * R * Cb, fun y hy => ?_⟩
    have h := circleIntegral.norm_integral_le_of_norm_le_const (c := c) (R := R)
      (f := fun w => exp (((σ * y : ℝ) : ℂ) * w) * b w) (C := Real.exp (σ * Y * y) * Cb) hR
      (fun w hw => by
        rw [norm_mul, norm_exp_real_mul]
        have hle : σ * y * w.re ≤ σ * Y * y := by
          have := mul_le_mul_of_nonneg_left (hY w hw) (mul_pos hσ hy).le
          linarith
        exact mul_le_mul (Real.exp_le_exp.2 hle) (hCb w hw) (norm_nonneg _) (Real.exp_pos _).le)
    calc _ ≤ 2 * Real.pi * R * (Real.exp (σ * Y * y) * Cb) := h
      _ = 2 * Real.pi * R * Cb * Real.exp (σ * Y * y) := by ring

/-- R6d-2 (inner step). For fixed `z` to the right of the circle, insert
`1/(w-z) = -σ∫₀^∞ e^{σy(w-z)}dy` and swap. -/
theorem inner_factor (b : ℂ → ℂ) (c : ℂ) (R σ δ : ℝ) (hR : 0 ≤ R) (hσ : 0 < σ) (hδ : 0 < δ)
    (hb : ContinuousOn b (Metric.sphere c R)) (z κ : ℂ)
    (hsep : ∀ w ∈ Metric.sphere c R, w.re - z.re ≤ -δ) :
    ∮ w in C(c, R), κ * b w * (1 / (w - z)) =
      -(σ : ℂ) * ∫ y in Ioi (0 : ℝ), exp (-((σ * y : ℝ) : ℂ) * z) * κ *
        ∮ w in C(c, R), exp (((σ * y : ℝ) : ℂ) * w) * b w := by
  obtain ⟨Cb, hCb⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hb
  have hbc : Continuous (fun φ : ℝ => b (circleMap c R φ)) :=
    hb.comp_continuous (continuous_circleMap c R) (fun φ => circleMap_mem_sphere c hR φ)
  have step1 : (∮ w in C(c, R), κ * b w * (1 / (w - z))) =
      ∮ w in C(c, R), κ * b w * (-(σ : ℂ) * ∫ y in Ioi (0 : ℝ), exp (((σ * y : ℝ) : ℂ) * (w - z))) := by
    refine circleIntegral.integral_congr hR (fun w hw => ?_)
    have hre : (w - z).re < 0 := by rw [Complex.sub_re]; linarith [hsep w hw]
    rw [inv_sub_eq_neg_integral w z σ hσ hre]
  rw [step1]
  unfold circleIntegral
  let F : ℝ → ℝ → ℂ := fun φ y => -(σ : ℂ) * (deriv (circleMap c R) φ *
    (κ * b (circleMap c R φ) * exp (((σ * y : ℝ) : ℂ) * (circleMap c R φ - z))))
  have hF : ∀ φ : ℝ, deriv (circleMap c R) φ • (κ * b (circleMap c R φ) * (-(σ : ℂ) *
      ∫ y in Ioi (0 : ℝ), exp (((σ * y : ℝ) : ℂ) * (circleMap c R φ - z)))) =
      ∫ y in Ioi (0 : ℝ), F φ y := by
    intro φ
    rw [smul_eq_mul]
    have e : deriv (circleMap c R) φ * (κ * b (circleMap c R φ) * (-(σ : ℂ) *
        ∫ y in Ioi (0 : ℝ), exp (((σ * y : ℝ) : ℂ) * (circleMap c R φ - z)))) =
        (-(σ : ℂ) * (deriv (circleMap c R) φ * (κ * b (circleMap c R φ)))) *
          ∫ y in Ioi (0 : ℝ), exp (((σ * y : ℝ) : ℂ) * (circleMap c R φ - z)) := by ring
    rw [e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [F]
    ring
  simp_rw [hF]
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap c R) p.1 := by
      simp only [deriv_circleMap]; exact ((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const
    have h3 : Continuous fun p : ℝ × ℝ => exp (((σ * p.2 : ℝ) : ℂ) * (circleMap c R p.1 - z)) :=
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)).mul
        (((continuous_circleMap c R).comp continuous_fst).sub continuous_const)).cexp
    exact continuous_const.mul (h1.mul ((continuous_const.mul (hbc.comp continuous_fst)).mul h3))
  have hFb : ∀ φ y : ℝ, 0 < y → ‖F φ y‖ ≤ (σ * (R * (‖κ‖ * Cb))) * Real.exp (-(σ * δ) * y) := by
    intro φ y hy
    have hw := circleMap_mem_sphere c hR φ
    simp only [F]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ, norm_mul,
      norm_deriv_circleMap' c R hR, norm_mul, norm_mul, norm_exp_real_mul]
    have hle : σ * y * (circleMap c R φ - z).re ≤ -(σ * δ) * y := by
      rw [Complex.sub_re]
      have := mul_le_mul_of_nonneg_left (hsep _ hw) (mul_pos hσ hy).le
      linarith
    have hE := Real.exp_le_exp.2 hle
    have hB := hCb _ hw
    have hk := norm_nonneg κ
    have h0 : 0 ≤ ‖b (circleMap c R φ)‖ := norm_nonneg _
    have hprod : ‖κ‖ * ‖b (circleMap c R φ)‖ * Real.exp (σ * y * (circleMap c R φ - z).re) ≤
        ‖κ‖ * Cb * Real.exp (-(σ * δ) * y) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB hk) hE (Real.exp_pos _).le
        (mul_nonneg hk (h0.trans hB))
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hR) hσ.le
    linarith
  rw [swap_interval_Ioi F hFc _ (σ * δ) (mul_pos hσ hδ) hFb, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun φ _ => ?_)
  simp only [F, smul_eq_mul]
  rw [mul_sub, sub_eq_add_neg, exp_add]
  ring_nf


theorem norm_exp_neg_real_mul (t : ℝ) (z : ℂ) :
    ‖exp (-((t : ℝ) : ℂ) * z)‖ = Real.exp (-(t * z.re)) := by
  rw [norm_exp, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]

/-- R6d-3 (outer step). -/
theorem outer_factor (a : ℂ → ℂ) (c : ℂ) (R σ X β CB : ℝ) (hR : 0 ≤ R) (hσ : 0 < σ) (hβX : β < X)
    (ha : ContinuousOn a (Metric.sphere c R)) (hX : ∀ z ∈ Metric.sphere c R, X ≤ z.re)
    (B : ℝ → ℂ) (hB : Continuous B) (hBb : ∀ y : ℝ, 0 < y → ‖B y‖ ≤ CB * Real.exp (σ * β * y)) :
    ∮ z in C(c, R), -(σ : ℂ) * ∫ y in Ioi (0 : ℝ), exp (-((σ * y : ℝ) : ℂ) * z) * a z * B y =
      -(σ : ℂ) * ∫ y in Ioi (0 : ℝ), (∮ z in C(c, R), exp (-((σ * y : ℝ) : ℂ) * z) * a z) * B y := by
  obtain ⟨Ca, hCa⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn ha
  have hac : Continuous (fun θ : ℝ => a (circleMap c R θ)) :=
    ha.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR θ)
  unfold circleIntegral
  let G : ℝ → ℝ → ℂ := fun θ y => -(σ : ℂ) * (deriv (circleMap c R) θ *
    (exp (-((σ * y : ℝ) : ℂ) * circleMap c R θ) * a (circleMap c R θ) * B y))
  have hG : ∀ θ : ℝ, deriv (circleMap c R) θ • (-(σ : ℂ) * ∫ y in Ioi (0 : ℝ),
      exp (-((σ * y : ℝ) : ℂ) * circleMap c R θ) * a (circleMap c R θ) * B y) =
      ∫ y in Ioi (0 : ℝ), G θ y := by
    intro θ
    rw [smul_eq_mul, ← mul_assoc, mul_comm (deriv (circleMap c R) θ), mul_assoc,
      ← integral_const_mul, ← integral_const_mul]
  simp_rw [hG]
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap c R) p.1 := by
      simp only [deriv_circleMap]; exact ((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const
    have h3 : Continuous fun p : ℝ × ℝ => exp (-((σ * p.2 : ℝ) : ℂ) * circleMap c R p.1) :=
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_snd)).neg.mul
        ((continuous_circleMap c R).comp continuous_fst)).cexp
    exact continuous_const.mul (h1.mul ((h3.mul (hac.comp continuous_fst)).mul (hB.comp continuous_snd)))
  have hGb : ∀ θ y : ℝ, 0 < y → ‖G θ y‖ ≤ (σ * (R * (Ca * CB))) * Real.exp (-(σ * (X - β)) * y) := by
    intro θ y hy
    have hz := circleMap_mem_sphere c hR θ
    simp only [G]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ, norm_mul,
      norm_deriv_circleMap' c R hR, norm_mul, norm_mul, norm_exp_neg_real_mul]
    have hle : -(σ * y * (circleMap c R θ).re) ≤ -(σ * X * y) := by
      have := mul_le_mul_of_nonneg_left (hX _ hz) (mul_pos hσ hy).le
      linarith
    have hE := Real.exp_le_exp.2 hle
    have hA := hCa _ hz
    have hBy := hBb y hy
    have hA0 : 0 ≤ ‖a (circleMap c R θ)‖ := norm_nonneg _
    have hB0 : 0 ≤ ‖B y‖ := norm_nonneg _
    have hCB0 : 0 ≤ CB * Real.exp (σ * β * y) := hB0.trans hBy
    have hprod : Real.exp (-(σ * y * (circleMap c R θ).re)) * ‖a (circleMap c R θ)‖ * ‖B y‖ ≤
        Real.exp (-(σ * X * y)) * Ca * (CB * Real.exp (σ * β * y)) :=
      mul_le_mul (mul_le_mul hE hA hA0 (Real.exp_pos _).le) hBy hB0
        (mul_nonneg (Real.exp_pos _).le (hA0.trans hA))
    have hexp : Real.exp (-(σ * X * y)) * Ca * (CB * Real.exp (σ * β * y)) =
        Ca * CB * Real.exp (-(σ * (X - β)) * y) := by
      rw [show -(σ * (X - β)) * y = -(σ * X * y) + σ * β * y by ring, Real.exp_add]; ring
    rw [hexp] at hprod
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hR) hσ.le
    nlinarith
  rw [swap_interval_Ioi G hGc _ (σ * (X - β)) (mul_pos hσ (by linarith)) hGb, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [G, smul_eq_mul]
  ring

/-- R6d. Double circle integral against `1/(w - z)` (Σ left of Γ) as a `y`-integral of products. -/
theorem circle_circle_factor (a b : ℂ → ℂ) (cΓ ρΓ cS ρS σ : ℝ) (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS)
    (hσ : 0 < σ) (hsep : cS + ρS < cΓ - ρΓ) (ha : ContinuousOn a (Metric.sphere (cΓ : ℂ) ρΓ))
    (hb : ContinuousOn b (Metric.sphere (cS : ℂ) ρS)) :
    (∮ z in C((cΓ : ℂ), ρΓ), ∮ w in C((cS : ℂ), ρS), a z * b w * (1 / (w - z))) =
      -(σ : ℂ) * ∫ y in Ioi (0 : ℝ),
        (∮ z in C((cΓ : ℂ), ρΓ), exp (-((σ * y : ℝ) : ℂ) * z) * a z) *
          (∮ w in C((cS : ℂ), ρS), exp (((σ * y : ℝ) : ℂ) * w) * b w) := by
  have hreS : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w.re ≤ cS + ρS := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    have h := Complex.abs_re_le_norm (w - cS)
    rw [hw, Complex.sub_re, ofReal_re] at h
    linarith [le_abs_self (w.re - cS)]
  have hreΓ : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, cΓ - ρΓ ≤ z.re := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have h := Complex.abs_re_le_norm (z - cΓ)
    rw [hz, Complex.sub_re, ofReal_re] at h
    linarith [neg_abs_le (z.re - cΓ)]
  have hδ : 0 < (cΓ - ρΓ) - (cS + ρS) := by linarith
  obtain ⟨hBc, CB, hCB⟩ := circle_exp_cont_bound b (cS : ℂ) ρS σ (cS + ρS) hρS hσ hb hreS
  rw [circleIntegral.integral_congr hρΓ (fun z hz => inner_factor b (cS : ℂ) ρS σ _ hρS hσ hδ hb z (a z)
    (fun w hw => by linarith [hreS w hw, hreΓ z hz]))]
  exact outer_factor a (cΓ : ℂ) ρΓ σ (cΓ - ρΓ) (cS + ρS) CB hρΓ hσ (by linarith) ha hreΓ _ hBc hCB


/-- `(p - z)^k g(z) = Π_{j<r} (π_j - z) / (1 - z)^r` when `π_j = p` for `j < k`. -/
theorem pc_pow_mul_gFn {r : ℕ} (k : ℕ) (hkr : k ≤ r) (π : Fin r → ℝ) (p : ℝ)
    (hp : ∀ j : Fin r, (j : ℕ) < k → π j = p) (z : ℂ) :
    ((p : ℂ) - z) ^ k * SpikedWishart.SoftEdge.gFn k π z = (∏ j, ((π j : ℂ) - z)) / (1 - z) ^ r := by
  unfold SpikedWishart.SoftEdge.gFn
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin r => (j : ℕ) < k)]
  have hc : ∀ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), ((π j : ℂ) - z) = (p : ℂ) - z :=
    fun j hj => by rw [hp j (Finset.mem_filter.1 hj).2]
  have h1 : ∏ j ∈ Finset.univ.filter (fun j : Fin r => (j : ℕ) < k), ((π j : ℂ) - z) =
      ((p : ℂ) - z) ^ k := by
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Fin.card_filter_val_lt, min_eq_right hkr]
  have h2 : Finset.univ.filter (fun j : Fin r => ¬ (j : ℕ) < k) =
      Finset.univ.filter (fun j : Fin r => k ≤ (j : ℕ)) := by
    ext j; simp
  rw [h1, h2]
  ring

open SpikedWishart.SoftEdge in
/-- R6f. Pointwise identity: the `K_{M,N}` integrand equals `A(z) B(w) / (w - z)` with `A`, `B`
the `𝓗`, `𝓙` integrands (at `u`, `v`). -/
theorem kernel_integrand_eq {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r ≤ N) (hkr : k ≤ r)
    (γ q σ u v η ζ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N)
    (hη : η * (M : ℝ) = mu γ * M + σ * u) (hζ : ζ * (M : ℝ) = mu γ * M + σ * v)
    (π : Fin N → ℝ) (π' : Fin r → ℝ) (hπ' : ∀ j : Fin r, π' j = π ⟨j, lt_of_lt_of_le j.2 hr⟩)
    (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1) (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (z w : ℂ) (hz0 : z ≠ 0) (hz1 : 1 - z ≠ 0) (hzπ : ∀ j, (π j : ℂ) - z ≠ 0)
    (hw0 : w ≠ 0) (hw1 : 1 - w ≠ 0) (hwz : w - z ≠ 0) :
    exp (-(η : ℂ) * M * (z - q) + (ζ : ℂ) * M * (w - q)) * (1 / (w - z)) * (z / w) ^ M *
        ∏ j, (((π j : ℂ) - w) / ((π j : ℂ) - z)) =
      (exp (-((σ * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
          (1 / (((pc γ : ℂ) - z) ^ k * gFn k π' z))) *
        (exp (((σ * v : ℝ) : ℂ) * (w - q)) * exp (-(M : ℂ) * fFn γ q w) *
          (((pc γ : ℂ) - w) ^ k * gFn k π' w)) * (1 / (w - z)) := by
  have hs : ∀ x : ℂ, ∏ j, ((π j : ℂ) - x) = (∏ j : Fin r, ((π' j : ℂ) - x)) * (1 - x) ^ (N - r) := by
    intro x
    rw [prod_split hr π h1 x]
    congr 1
    exact Finset.prod_congr rfl (fun j _ => by rw [hπ' j])
  have hQ : ∏ j : Fin r, ((π' j : ℂ) - z) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun j _ => by rw [hπ' j]; exact hzπ _)
  have hexp : exp (-(η : ℂ) * M * (z - q) + (ζ : ℂ) * M * (w - q)) =
      exp (-((σ * u : ℝ) : ℂ) * (z - q)) * exp (-(M : ℂ) * (mu γ : ℂ) * (z - q)) *
        (exp (((σ * v : ℝ) : ℂ) * (w - q)) * exp ((M : ℂ) * (mu γ : ℂ) * (w - q))) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    have hη' : (η : ℂ) * M = (mu γ : ℂ) * M + (σ : ℂ) * u := by exact_mod_cast hη
    have hζ' : (ζ : ℂ) * M = (mu γ : ℂ) * M + (σ : ℂ) * v := by exact_mod_cast hζ
    push_cast
    linear_combination (-(z - q)) * hη' + (w - q) * hζ'
  have hNz : (1 - z) ^ N = (1 - z) ^ r * (1 - z) ^ (N - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
  have hNw : (1 - w) ^ N = (1 - w) ^ r * (1 - w) ^ (N - r) := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
  rw [exp_M_fFn γ q M N hM hN hγ z hz0 hz1, exp_neg_M_fFn γ q M N hM hN hγ w hw0 hw1,
    pc_pow_mul_gFn k hkr π' (pc γ) hpc z, pc_pow_mul_gFn k hkr π' (pc γ) hpc w,
    Finset.prod_div_distrib, hs w, hs z, hexp, hNz, hNw]
  have hz1r : (1 - z) ^ r ≠ 0 := pow_ne_zero _ hz1
  have hz1n : (1 - z) ^ (N - r) ≠ 0 := pow_ne_zero _ hz1
  have hw1r : (1 - w) ^ r ≠ 0 := pow_ne_zero _ hw1
  have hwM : w ^ M ≠ 0 := pow_ne_zero _ hw0
  rw [div_pow]
  field_simp


theorem re_le_of_mem_sphere (c R : ℝ) (w : ℂ) (hw : w ∈ Metric.sphere (c : ℂ) R) : w.re ≤ c + R := by
  rw [mem_sphere_iff_norm] at hw
  have h := Complex.abs_re_le_norm (w - c)
  rw [hw, Complex.sub_re, ofReal_re] at h
  linarith [le_abs_self (w.re - c)]

theorem le_re_of_mem_sphere (c R : ℝ) (z : ℂ) (hz : z ∈ Metric.sphere (c : ℂ) R) : c - R ≤ z.re := by
  rw [mem_sphere_iff_norm] at hz
  have h := Complex.abs_re_le_norm (z - c)
  rw [hz, Complex.sub_re, ofReal_re] at h
  linarith [neg_abs_le (z.re - c)]

theorem nu_mul_pos (γ : ℝ) (hγ : 0 < γ) (M : ℕ) (hM : 0 < M) :
    0 < SpikedWishart.SoftEdge.nu γ * (M : ℝ) ^ (1 / 3 : ℝ) := by
  unfold SpikedWishart.SoftEdge.nu
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  exact mul_pos (div_pos (Real.rpow_pos_of_pos (by linarith) _) hγ) (Real.rpow_pos_of_pos hM' _)

open SpikedWishart.SoftEdge in
/-- The `𝓗` integrand is continuous where `z ≠ 0, 1, π_j` (via the log-free form). -/
theorem A_contOn {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hkr : k ≤ r)
    (γ q t : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (π' : Fin r → ℝ)
    (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (S : Set ℂ) (hS : ∀ z ∈ S, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π' j : ℂ) - z ≠ 0) :
    ContinuousOn (fun z => exp (-((t : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
          (1 / (((pc γ : ℂ) - z) ^ k * gFn k π' z))) S := by
  have hc : ContinuousOn (fun z : ℂ => exp (-((t : ℝ) : ℂ) * (z - q)) *
      exp (-(M : ℂ) * (mu γ : ℂ) * (z - q)) * z ^ M * (1 - z) ^ r * ((1 - z) ^ N)⁻¹ *
        (∏ j, ((π' j : ℂ) - z))⁻¹) S := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (by fun_prop : Continuous fun z : ℂ => exp (-((t : ℝ) : ℂ) * (z - q)) *
        exp (-(M : ℂ) * (mu γ : ℂ) * (z - q)) * z ^ M * (1 - z) ^ r).continuousOn
    · exact ContinuousOn.inv₀ (by fun_prop) (fun z hz => pow_ne_zero _ (hS z hz).2.1)
    · exact ContinuousOn.inv₀ (by fun_prop)
        (fun z hz => Finset.prod_ne_zero_iff.2 (fun j _ => (hS z hz).2.2 j))
  refine hc.congr (fun z hz => ?_)
  obtain ⟨h0, h1, h2⟩ := hS z hz
  have hQ : ∏ j, ((π' j : ℂ) - z) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun j _ => h2 j)
  have hN1 : (1 - z) ^ N ≠ 0 := pow_ne_zero _ h1
  have hr1 : (1 - z) ^ r ≠ 0 := pow_ne_zero _ h1
  simp only
  rw [exp_M_fFn γ q M N hM hN hγ z h0 h1, pc_pow_mul_gFn k hkr π' (pc γ) hpc z]
  field_simp

open SpikedWishart.SoftEdge in
/-- The `𝓙` integrand is continuous where `w ≠ 0, 1`. -/
theorem B_contOn {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hkr : k ≤ r)
    (γ q t : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (π' : Fin r → ℝ)
    (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (S : Set ℂ) (hS : ∀ w ∈ S, w ≠ 0 ∧ 1 - w ≠ 0) :
    ContinuousOn (fun w => exp (((t : ℝ) : ℂ) * (w - q)) * exp (-(M : ℂ) * fFn γ q w) *
          (((pc γ : ℂ) - w) ^ k * gFn k π' w)) S := by
  have hc : ContinuousOn (fun w : ℂ => exp (((t : ℝ) : ℂ) * (w - q)) *
      exp ((M : ℂ) * (mu γ : ℂ) * (w - q)) * (1 - w) ^ N * (∏ j, ((π' j : ℂ) - w)) *
        (w ^ M)⁻¹ * ((1 - w) ^ r)⁻¹) S := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (by fun_prop : Continuous fun w : ℂ => exp (((t : ℝ) : ℂ) * (w - q)) *
        exp ((M : ℂ) * (mu γ : ℂ) * (w - q)) * (1 - w) ^ N * ∏ j, ((π' j : ℂ) - w)).continuousOn
    · exact ContinuousOn.inv₀ (by fun_prop) (fun w hw => pow_ne_zero _ (hS w hw).1)
    · exact ContinuousOn.inv₀ (by fun_prop) (fun w hw => pow_ne_zero _ (hS w hw).2)
  refine hc.congr (fun w hw => ?_)
  obtain ⟨h0, h1⟩ := hS w hw
  have hM0 : w ^ M ≠ 0 := pow_ne_zero _ h0
  have hr1 : (1 - w) ^ r ≠ 0 := pow_ne_zero _ h1
  simp only
  rw [exp_neg_M_fFn γ q M N hM hN hγ w h0 h1, pc_pow_mul_gFn k hkr π' (pc γ) hpc w]
  field_simp

open SpikedWishart.SoftEdge in
theorem Hcal_shift {r : ℕ} (γ q : ℝ) (M k : ℕ) (π' : Fin r → ℝ) (c ρ u y σ : ℝ)
    (hσ : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) :
    Hcal γ q M k π' c ρ (u + y) =
      ((σ / (2 * Real.pi) : ℝ) : ℂ) * exp (((σ * y : ℝ) : ℂ) * q) *
        ∮ z in C((c : ℂ), ρ), exp (-((σ * y : ℝ) : ℂ) * z) *
          (exp (-((σ * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
            (1 / (((pc γ : ℂ) - z) ^ k * gFn k π' z))) := by
  unfold Hcal
  rw [hσ, mul_assoc ((σ / (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [← circleIntegral.integral_const_mul]
  refine congrArg (fun f => circleIntegral f (c : ℂ) ρ) (funext fun z => ?_)
  have e : exp (-((σ * (u + y) : ℝ) : ℂ) * (z - q)) = exp (((σ * y : ℝ) : ℂ) * q) *
      exp (-((σ * y : ℝ) : ℂ) * z) * exp (-((σ * u : ℝ) : ℂ) * (z - q)) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [e]; ring

open SpikedWishart.SoftEdge in
theorem Jcal_shift {r : ℕ} (γ q : ℝ) (M k : ℕ) (π' : Fin r → ℝ) (c ρ v y σ : ℝ)
    (hσ : nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ) :
    Jcal γ q M k π' c ρ (v + y) =
      ((σ / (2 * Real.pi) : ℝ) : ℂ) * exp (-((σ * y : ℝ) : ℂ) * q) *
        ∮ w in C((c : ℂ), ρ), exp (((σ * y : ℝ) : ℂ) * w) *
          (exp (((σ * v : ℝ) : ℂ) * (w - q)) * exp (-(M : ℂ) * fFn γ q w) *
            (((pc γ : ℂ) - w) ^ k * gFn k π' w)) := by
  unfold Jcal
  rw [hσ, mul_assoc ((σ / (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [← circleIntegral.integral_const_mul]
  refine congrArg (fun f => circleIntegral f (c : ℂ) ρ) (funext fun w => ?_)
  have e : exp (((σ * (v + y) : ℝ) : ℂ) * (w - q)) = exp (-((σ * y : ℝ) : ℂ) * q) *
      exp (((σ * y : ℝ) : ℂ) * w) * exp (((σ * v : ℝ) : ℂ) * (w - q)) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  rw [e]; ring

theorem prod_cancel_aux (c e1 e2 I1 I2 : ℂ) (h : e1 * e2 = 1) :
    c * e1 * I1 * (c * e2 * I2) = c ^ 2 * (I1 * I2) := by
  linear_combination (c ^ 2 * I1 * I2) * h

open SpikedWishart.SoftEdge in
/-- R6g. `s K_{M,N}(µ + s u, µ + s v) = Re ∫₀^∞ 𝓗(u+y) 𝓙(v+y) dy` with `s = νM^{1/3}/M`. -/
theorem kernel_factor {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r ≤ N) (hkr : k ≤ r)
    (γ q cΓ ρΓ cS ρS u v η ζ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (hγ0 : 0 < γ)
    (hη : η * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u)
    (hζ : ζ * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v)
    (π : Fin N → ℝ) (π' : Fin r → ℝ) (hπ' : ∀ j : Fin r, π' j = π ⟨j, lt_of_lt_of_le j.2 hr⟩)
    (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1) (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hΓ : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π j : ℂ) - z ≠ 0)
    (hSig : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 ∧ 1 - w ≠ 0) :
    nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      (∫ y in Ioi (0 : ℝ), Hcal γ q M k π' cΓ ρΓ (u + y) * Jcal γ q M k π' cS ρS (v + y)).re := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, nu γ * (M : ℝ) ^ (1 / 3 : ℝ) = σ := ⟨_, rfl⟩
  have hσ : 0 < σ := hσdef ▸ nu_mul_pos γ hγ0 M hM
  have hHJ : ∀ y : ℝ, Hcal γ q M k π' cΓ ρΓ (u + y) * Jcal γ q M k π' cS ρS (v + y) =
      ((σ / (2 * Real.pi) : ℝ) : ℂ) ^ 2 *
        ((∮ z in C((cΓ : ℂ), ρΓ), exp (-((σ * y : ℝ) : ℂ) * z) *
          (exp (-((σ * u : ℝ) : ℂ) * (z - q)) * exp ((M : ℂ) * fFn γ q z) *
            (1 / (((pc γ : ℂ) - z) ^ k * gFn k π' z)))) *
         (∮ w in C((cS : ℂ), ρS), exp (((σ * y : ℝ) : ℂ) * w) *
          (exp (((σ * v : ℝ) : ℂ) * (w - q)) * exp (-(M : ℂ) * fFn γ q w) *
            (((pc γ : ℂ) - w) ^ k * gFn k π' w)))) := by
    intro y
    rw [Hcal_shift γ q M k π' cΓ ρΓ u y σ hσdef, Jcal_shift γ q M k π' cS ρS v y σ hσdef]
    refine prod_cancel_aux _ _ _ _ _ ?_
    rw [← exp_add, show ((σ * y : ℝ) : ℂ) * q + -((σ * y : ℝ) : ℂ) * q = 0 by ring, exp_zero]
  rw [hσdef] at hη hζ ⊢
  have hΓ' : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π' j : ℂ) - z ≠ 0 :=
    fun z hz => ⟨(hΓ z hz).1, (hΓ z hz).2.1, fun j => by rw [hπ' j]; exact (hΓ z hz).2.2 _⟩
  have hAc := A_contOn k M hM hN hkr γ q (σ * u) hγ π' hpc _ hΓ'
  have hBc := B_contOn k M hM hN hkr γ q (σ * v) hγ π' hpc _ hSig
  have hwz : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w - z ≠ 0 := by
    intro z hz w hw h
    have h' := congrArg Complex.re h
    rw [Complex.sub_re, Complex.zero_re] at h'
    linarith [re_le_of_mem_sphere cS ρS w hw, le_re_of_mem_sphere cΓ ρΓ z hz]
  unfold kernelKMN
  rw [circleIntegral.integral_congr hρΓ (fun z hz => circleIntegral.integral_congr hρS (fun w hw =>
    kernel_integrand_eq k M hM hN hr hkr γ q σ u v η ζ hγ hη hζ π π' hπ' h1 hpc z w (hΓ z hz).1
      (hΓ z hz).2.1 (hΓ z hz).2.2 (hSig w hw).1 (hSig w hw).2 (hwz z hz w hw)))]
  rw [circle_circle_factor _ _ cΓ ρΓ cS ρS σ hρΓ hρS hσ hsep hAc hBc]
  simp_rw [hHJ]
  rw [integral_const_mul, ← Complex.re_ofReal_mul]
  congr 1
  have hI : (2 * (Real.pi : ℂ) * I) ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
    ring_nf; rw [I_sq]; ring
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [hI]
  push_cast
  field_simp
  ring


/-- Continuity of a parametric circle integral `u ↦ ∮ E(u,z) g(z) dz`. -/
theorem circle_param_cont (F E : ℝ → ℂ → ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hg : ContinuousOn g (Metric.sphere c R)) (hE : Continuous (Function.uncurry E))
    (hFE : ∀ u : ℝ, ∀ z ∈ Metric.sphere c R, F u z = E u z * g z) :
    Continuous (fun u : ℝ => ∮ z in C(c, R), F u z) := by
  have e : (fun u : ℝ => ∮ z in C(c, R), F u z) = fun u => ∮ z in C(c, R), E u z * g z :=
    funext fun u => circleIntegral.integral_congr hR (fun z hz => hFE u z hz)
  rw [e]
  have hgc : Continuous (fun φ : ℝ => g (circleMap c R φ)) :=
    hg.comp_continuous (continuous_circleMap c R) (fun φ => circleMap_mem_sphere c hR φ)
  unfold circleIntegral
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * Real.pi)
  have h1 : Continuous fun p : ℝ × ℝ => deriv (circleMap c R) p.2 := by
    simp only [deriv_circleMap]; exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have h3 : Continuous fun p : ℝ × ℝ => E p.1 (circleMap c R p.2) :=
    hE.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
  exact h1.smul (h3.mul (hgc.comp continuous_snd))

open SpikedWishart.SoftEdge in
theorem Hcal_continuous {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hkr : k ≤ r)
    (γ q cΓ ρΓ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (π' : Fin r → ℝ)
    (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ) (hρ : 0 ≤ ρΓ)
    (hS : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π' j : ℂ) - z ≠ 0) :
    Continuous (Hcal γ q M k π' cΓ ρΓ) := by
  unfold Hcal
  refine continuous_const.mul (circle_param_cont _
    (fun u z => exp (-((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u : ℝ) : ℂ) * (z - q)))
    _ (cΓ : ℂ) ρΓ hρ (A_contOn k M hM hN hkr γ q 0 hγ π' hpc _ hS) (by fun_prop) ?_)
  intro u z _
  simp only [ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

open SpikedWishart.SoftEdge in
theorem Jcal_continuous {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hkr : k ≤ r)
    (γ q cS ρS : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (π' : Fin r → ℝ)
    (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ) (hρ : 0 ≤ ρS)
    (hS : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 ∧ 1 - w ≠ 0) :
    Continuous (Jcal γ q M k π' cS ρS) := by
  unfold Jcal
  refine continuous_const.mul (circle_param_cont _
    (fun v w => exp (((nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v : ℝ) : ℂ) * (w - q)))
    _ (cS : ℂ) ρS hρ (B_contOn k M hM hN hkr γ q 0 hγ π' hpc _ hS) (by fun_prop) ?_)
  intro v w _
  simp only [ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  ring

open SpikedWishart.SoftEdge in
theorem kernelKMN_factorization_aux {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r ≤ N) (hkr : k ≤ r)
    (γ q cΓ ρΓ cS ρS u v η ζ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (hγ0 : 0 < γ)
    (hη : η * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u)
    (hζ : ζ * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v)
    (π : Fin N → ℝ) (π' : Fin r → ℝ) (hπ' : ∀ j : Fin r, π' j = π ⟨j, lt_of_lt_of_le j.2 hr⟩)
    (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1) (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hΓ : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π j : ℂ) - z ≠ 0)
    (hSig : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 ∧ 1 - w ≠ 0) :
    nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      (∫ y in Set.Ioi (0 : ℝ), Hcal γ q M k π' cΓ ρΓ (u + y) * Jcal γ q M k π' cS ρS (v + y)).re ∧
    Continuous (Hcal γ q M k π' cΓ ρΓ) ∧ Continuous (Jcal γ q M k π' cS ρS) :=
  ⟨kernel_factor k M hM hN hr hkr γ q cΓ ρΓ cS ρS u v η ζ hγ hγ0 hη hζ π π' hπ' h1 hpc hρΓ hρS hsep hΓ hSig,
    Hcal_continuous k M hM hN hkr γ q cΓ ρΓ hγ π' hpc hρΓ (fun z hz => ⟨(hΓ z hz).1, (hΓ z hz).2.1,
      fun j => by rw [hπ' j]; exact (hΓ z hz).2.2 _⟩),
    Jcal_continuous k M hM hN hkr γ q cS ρS hγ π' hpc hρS hSig⟩

end Lib5e

open SpikedWishart.SoftEdge MeasureTheory in
theorem solution {N r : ℕ} (k M : ℕ) (hM : 0 < M) (hN : 0 < N) (hr : r ≤ N) (hkr : k ≤ r)
    (γ q cΓ ρΓ cS ρS u v η ζ : ℝ) (hγ : γ ^ 2 = (M : ℝ) / N) (hγ0 : 0 < γ)
    (hη : η * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * u)
    (hζ : ζ * (M : ℝ) = mu γ * M + nu γ * (M : ℝ) ^ (1 / 3 : ℝ) * v)
    (π : Fin N → ℝ) (π' : Fin r → ℝ) (hπ' : ∀ j : Fin r, π' j = π ⟨j, lt_of_lt_of_le j.2 hr⟩)
    (h1 : ∀ j : Fin N, r ≤ (j : ℕ) → π j = 1) (hpc : ∀ j : Fin r, (j : ℕ) < k → π' j = pc γ)
    (hρΓ : 0 ≤ ρΓ) (hρS : 0 ≤ ρS) (hsep : cS + ρS < cΓ - ρΓ)
    (hΓ : ∀ z ∈ Metric.sphere (cΓ : ℂ) ρΓ, z ≠ 0 ∧ 1 - z ≠ 0 ∧ ∀ j, (π j : ℂ) - z ≠ 0)
    (hSig : ∀ w ∈ Metric.sphere (cS : ℂ) ρS, w ≠ 0 ∧ 1 - w ≠ 0) :
    nu γ * (M : ℝ) ^ (1 / 3 : ℝ) / M * kernelKMN M π q cΓ ρΓ cS ρS η ζ =
      (∫ y in Set.Ioi (0 : ℝ), Hcal γ q M k π' cΓ ρΓ (u + y) * Jcal γ q M k π' cS ρS (v + y)).re ∧
    Continuous (Hcal γ q M k π' cΓ ρΓ) ∧ Continuous (Jcal γ q M k π' cS ρS) := by
  exact Lib5e.kernelKMN_factorization_aux k M hM hN hr hkr γ q cΓ ρΓ cS ρS u v η ζ hγ hγ0 hη hζ π π' hπ' h1 hpc hρΓ hρS hsep hΓ hSig
