-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:47:07.405993+00:00
-- url     : https://prove2.me/submissions/518af6a3-b158-40a6-92e2-8aeb0a15cc6d

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Theorems.Thm_SmoothAmbEq_Gaussian_lemma_C_2

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace SmoothAmbC1Aux

open SmoothAmbEq.Gaussian

lemma zeta_pos (M : Model) {u : ℝ} (hu : 0 ≤ u) : 0 < M.ζ u := by
  have := M.hσ; have := M.hσ₀
  unfold Model.ζ; positivity

lemma zeta_le (M : Model) {u : ℝ} (hu : 0 ≤ u) : M.ζ u ≤ M.σ₀ ^ 2 := by
  have h1 := M.hσ; have h2 := M.hσ₀
  unfold Model.ζ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hu (sq_nonneg M.σ₀), sq_nonneg M.σ₀, mul_nonneg (sq_nonneg M.σ₀) (mul_nonneg hu (sq_nonneg M.σ₀))]

lemma zeta_anti (M : Model) {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) : M.ζ u ≤ M.ζ t := by
  have h1 := M.hσ; have h2 := M.hσ₀
  unfold Model.ζ
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [sq_nonneg M.σ₀]

/-- The exact Gaussian moment of `β^z_u`. -/
lemma key {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (z t β u a : ℝ) (ht : 0 ≤ t) (htu : t ≤ u)
    (hx : 2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t)) < 1) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * (betaZ M W z t β u ω) ^ 2)) ∂P) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t))) *
        Real.exp ((2 * a * (M.ζ u * (β / M.ζ t + z * (u - t) / M.σ ^ 2)) ^ 2) /
          (2 * (1 - 2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t)))))) := by
  set μ := M.ζ u * (β / M.ζ t + z * (u - t) / M.σ ^ 2) with hμ
  set c := M.ζ u / M.σ with hc
  have hσ := M.hσ
  have hlaw := hW.hasLaw_sub u.toNNReal t.toNNReal
  have hd : (nndist (u.toNNReal : ℝ) (t.toNNReal : ℝ) : ℝ) = u - t := by
    rw [coe_nndist, Real.dist_eq, Real.coe_toNNReal _ (ht.trans htu), Real.coe_toNNReal _ ht,
      abs_of_nonneg (by linarith)]
  have hbeta : ∀ ω, betaZ M W z t β u ω = μ + c * ((W u.toNNReal - W t.toNNReal) ω) := by
    intro ω
    simp only [betaZ, Pi.sub_apply, hμ, hc]
    field_simp
  simp_rw [hbeta]
  set g : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (a * x ^ 2 + 0 * x)) with hg
  have hgm : Measurable g := by
    simp only [hg]; fun_prop
  have h1 : (∫⁻ ω, ENNReal.ofReal (Real.exp (a * (μ + c * ((W u.toNNReal - W t.toNNReal) ω)) ^ 2)) ∂P)
      = ∫⁻ y, g (μ + c * y) ∂(gaussianReal 0 (nndist (u.toNNReal : ℝ) (t.toNNReal : ℝ))) := by
    refine Eq.trans ?_ (hlaw.lintegral_comp (f := fun y => g (μ + c * y))
      (hgm.comp (by fun_prop)).aemeasurable)
    simp [hg]
  rw [h1]
  have h2 : (∫⁻ y, g (μ + c * y) ∂(gaussianReal 0 (nndist (u.toNNReal : ℝ) (t.toNNReal : ℝ))))
      = ∫⁻ x, g x ∂(((gaussianReal 0 (nndist (u.toNNReal : ℝ) (t.toNNReal : ℝ))).map
          (fun y => c * y)).map (fun y => μ + y)) := by
    have hm2 : Measurable (fun y => g (μ + y)) := hgm.comp (by fun_prop)
    rw [lintegral_map hgm (by fun_prop), lintegral_map hm2 (by fun_prop)]
  rw [h2, gaussianReal_map_const_mul, gaussianReal_map_const_add]
  rw [((lemma_C_2 _ a 0 _).1 ?_).1]
  · congr 1
    simp only [NNReal.coe_mul, NNReal.coe_mk, hd]
    congr 2
    ring
  · simp only [NNReal.coe_mul, NNReal.coe_mk, hd]
    exact hx

/-- Elementary bounds on the right-hand side of `key`. -/
lemma bound (M : Model) (z t β u a h : ℝ) (ht : 0 ≤ t) (htu : t ≤ u) (hd : u - t ≤ h)
    (ha : 0 ≤ a) (hx : 2 * a * (M.σ₀ ^ 4 * h / M.σ ^ 2) ≤ 1 / 4) :
    2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t)) < 1 ∧
    1 / Real.sqrt (1 - 2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t))) *
        Real.exp ((2 * a * (M.ζ u * (β / M.ζ t + z * (u - t) / M.σ ^ 2)) ^ 2) /
          (2 * (1 - 2 * a * ((M.ζ u / M.σ) ^ 2 * (u - t)))))
      ≤ 4 / 3 * Real.exp (4 / 3 * a * (2 * β ^ 2 + 2 * (M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4) * z ^ 2)) := by
  have hσ := M.hσ
  have hu : 0 ≤ u := ht.trans htu
  have hzu := zeta_pos M hu
  have hzt := zeta_pos M ht
  have hzle := zeta_le M hu
  have hanti := zeta_anti M ht htu
  have hd0 : 0 ≤ u - t := by linarith
  have hh : 0 ≤ h := hd0.trans hd
  set v := (M.ζ u / M.σ) ^ 2 * (u - t) with hv
  have hv0 : 0 ≤ v := by positivity
  have hzsq : M.ζ u ^ 2 ≤ M.σ₀ ^ 4 := by
    have : M.ζ u ^ 2 ≤ (M.σ₀ ^ 2) ^ 2 := pow_le_pow_left₀ hzu.le hzle 2
    simpa [← pow_mul] using this
  have hvle : v ≤ M.σ₀ ^ 4 * h / M.σ ^ 2 := by
    rw [hv, div_pow, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul hzsq hd hd0 (by positivity)
  set x := 2 * a * v with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 4 := le_trans (by rw [hxdef]; exact mul_le_mul_of_nonneg_left hvle (by positivity)) hx
  refine ⟨by linarith, ?_⟩
  have hsq : 3 / 4 ≤ Real.sqrt (1 - x) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hfac : 1 / Real.sqrt (1 - x) ≤ 4 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  set μ := M.ζ u * (β / M.ζ t + z * (u - t) / M.σ ^ 2) with hμ
  have hμsq : μ ^ 2 ≤ 2 * β ^ 2 + 2 * (M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4) * z ^ 2 := by
    have hp : (M.ζ u * (β / M.ζ t)) ^ 2 ≤ β ^ 2 := by
      have hr : M.ζ u / M.ζ t ≤ 1 := (div_le_one hzt).2 hanti
      have hr0 : 0 ≤ M.ζ u / M.ζ t := by positivity
      have : (M.ζ u * (β / M.ζ t)) ^ 2 = (M.ζ u / M.ζ t) ^ 2 * β ^ 2 := by ring
      rw [this]
      have : (M.ζ u / M.ζ t) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg β]
    have hq : (M.ζ u * (z * (u - t) / M.σ ^ 2)) ^ 2 ≤ M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4 * z ^ 2 := by
      have : (M.ζ u * (z * (u - t) / M.σ ^ 2)) ^ 2 = M.ζ u ^ 2 * (u - t) ^ 2 / M.σ ^ 4 * z ^ 2 := by
        field_simp
      rw [this]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg z)
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hzsq (pow_le_pow_left₀ hd0 hd 2) (by positivity) (by positivity)
    have : μ = M.ζ u * (β / M.ζ t) + M.ζ u * (z * (u - t) / M.σ ^ 2) := by rw [hμ]; ring
    rw [this]
    nlinarith [sq_nonneg (M.ζ u * (β / M.ζ t) - M.ζ u * (z * (u - t) / M.σ ^ 2))]
  have hexp : (2 * a * μ ^ 2) / (2 * (1 - x)) ≤
      4 / 3 * a * (2 * β ^ 2 + 2 * (M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4) * z ^ 2) := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : a * μ ^ 2 ≤ a * (2 * β ^ 2 + 2 * (M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4) * z ^ 2) :=
      mul_le_mul_of_nonneg_left hμsq ha
    have h2 : 0 ≤ a * μ ^ 2 := by positivity
    nlinarith
  calc 1 / Real.sqrt (1 - x) * Real.exp ((2 * a * μ ^ 2) / (2 * (1 - x)))
      ≤ 4 / 3 * Real.exp (4 / 3 * a * (2 * β ^ 2 + 2 * (M.σ₀ ^ 4 * h ^ 2 / M.σ ^ 4) * z ^ 2)) :=
        mul_le_mul hfac (Real.exp_le_exp.2 hexp) (by positivity) (by norm_num)

/-- Left-endpoint Riemann sums of a continuous function converge to its integral. -/
lemma riemann (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
      (b - a) / (n + 1) * f (a + i * ((b - a) / (n + 1)))) atTop (𝓝 (∫ x in a..b, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hba : 0 < b - a := by linarith
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδf⟩ := huc (ε / (2 * (b - a))) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N, fun n hn => ?_⟩
  set k := (b - a) / (n + 1) with hk
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hk0 : 0 < k := by positivity
  have hkδ : k < δ := by
    rw [hk, div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hδ] at hN
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  set x : ℕ → ℝ := fun i => a + i * k with hx
  have hxmem : ∀ i, i ≤ n + 1 → x i ∈ Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ n + 1 := by exact_mod_cast hi
    constructor
    · simp only [hx]; have : (0:ℝ) ≤ i * k := by positivity
      linarith
    · simp only [hx]
      have : (i : ℝ) * k ≤ (n + 1) * k := mul_le_mul_of_nonneg_right hi' hk0.le
      have h2 : (n + 1 : ℝ) * k = b - a := by rw [hk]; field_simp
      linarith
  have hxsucc : ∀ i : ℕ, x (i + 1) = x i + k := by
    intro i; simp only [hx]; push_cast; ring
  have hxlast : x (n + 1) = b := by
    simp only [hx]; push_cast; rw [hk]; field_simp; ring
  have hsub : ∀ i, i < n + 1 → uIcc (x i) (x (i + 1)) ⊆ Icc a b := by
    intro i hi
    rw [uIcc_of_le (by rw [hxsucc]; linarith)]
    exact Icc_subset_Icc (hxmem i hi.le).1 (hxmem (i + 1) hi).2
  have hint : ∀ i < n + 1, IntervalIntegrable f MeasureTheory.volume (x i) (x (i + 1)) :=
    fun i hi => (hf.mono (hsub i hi)).intervalIntegrable
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have hx0 : x 0 = a := by simp [hx]
  rw [hx0, hxlast] at hsum
  rw [← hsum, dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖k * f (a + i * k) - ∫ u in x i..x (i + 1), f u‖ ≤ ε / (2 * (b - a)) * k := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hconst : k * f (a + i * k) = ∫ _ in x i..x (i + 1), f (x i) := by
      rw [intervalIntegral.integral_const, hxsucc]; simp [hx, smul_eq_mul]
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint i hi)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x i) (b := x (i + 1))
      (C := ε / (2 * (b - a))) (f := fun u => f (x i) - f u) ?_
    · rw [hxsucc, add_sub_cancel_left, abs_of_pos hk0] at this
      rw [hxsucc]; exact this
    · intro u hu
      rw [uIoc_of_le (by rw [hxsucc]; linarith)] at hu
      rw [hxsucc] at hu
      have hu' : u ∈ Icc a b := hsub i hi (by
        rw [uIcc_of_le (by rw [hxsucc]; linarith), hxsucc]; exact ⟨hu.1.le, hu.2⟩)
      have := hδf (x i) (hxmem i hi.le) u hu' (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
      rw [Real.dist_eq] at this
      exact this.le
  calc ‖∑ i ∈ Finset.range (n + 1), (k * f (a + i * k) - ∫ u in x i..x (i + 1), f u)‖
      ≤ ∑ i ∈ Finset.range (n + 1), ‖k * f (a + i * k) - ∫ u in x i..x (i + 1), f u‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), ε / (2 * (b - a)) * k := Finset.sum_le_sum hterm
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hk]; push_cast; field_simp
    _ < ε := by linarith

lemma aem_beta {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (z t β u : ℝ) :
    AEMeasurable (fun ω => betaZ M W z t β u ω) P := by
  have h1 := hW.aemeasurable u.toNNReal
  have h2 := hW.aemeasurable t.toNNReal
  unfold betaZ
  fun_prop

lemma aem_exp {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (z t β u a : ℝ) :
    AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (a * (betaZ M W z t β u ω) ^ 2))) P :=
  (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (a * x ^ 2))).comp_aemeasurable
    (aem_beta M P W hW z t β u)

lemma cont_beta {Ω : Type*} (M : Model) (W : ℝ≥0 → Ω → ℝ) (z t β : ℝ) (ω : Ω)
    (hω : Continuous (fun s => W s ω)) (a b : ℝ) (ha : 0 ≤ a) :
    ContinuousOn (fun u => (betaZ M W z t β u ω) ^ 2) (Icc a b) := by
  have hσ := M.hσ; have hσ₀ := M.hσ₀
  have hζ : ContinuousOn M.ζ (Icc a b) := by
    unfold Model.ζ
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro u hu
    have : 0 ≤ u := ha.trans hu.1
    positivity
  have hWc : Continuous (fun u : ℝ => W u.toNNReal ω) := hω.comp continuous_real_toNNReal
  unfold betaZ
  apply ContinuousOn.pow
  apply hζ.mul
  exact (by fun_prop : Continuous fun u : ℝ =>
    β / M.ζ t + z * (u - t) / M.σ ^ 2 + (W u.toNNReal ω - W t.toNNReal ω) / M.σ).continuousOn


lemma arith3 (C ε h L β z σ₀ σ : ℝ) (hC : 0 < C) (hh1 : h ≤ 1) (hL0 : 0 ≤ L)
    (hLh : L ≤ h) (hB : 3 * C * h ≤ ε) (hD : 3 * C * σ₀ ^ 4 * h / σ ^ 4 ≤ ε) (hσ : 0 < σ) :
    4 / 3 * (C * L) * (2 * β ^ 2 + 2 * (σ₀ ^ 4 * h ^ 2 / σ ^ 4) * z ^ 2) ≤ ε * (z ^ 2 + β ^ 2) := by
  have hh0 : 0 ≤ h := hL0.trans hLh
  have hc0 : 0 ≤ C * σ₀ ^ 4 / σ ^ 4 := by positivity
  have hLh2 : L * h ^ 2 ≤ h := by
    have : L * h ^ 2 ≤ 1 * (h * h) := by
      rw [sq]; exact mul_le_mul (hLh.trans hh1) le_rfl (by positivity) (by norm_num)
    have : h * h ≤ h := by nlinarith
    linarith
  have e1 : 4 / 3 * (C * L) * (2 * β ^ 2 + 2 * (σ₀ ^ 4 * h ^ 2 / σ ^ 4) * z ^ 2)
      = (8 / 3 * C * L) * β ^ 2 + (8 / 3 * (L * h ^ 2) * (C * σ₀ ^ 4 / σ ^ 4)) * z ^ 2 := by ring
  have e2 : 3 * C * σ₀ ^ 4 * h / σ ^ 4 = 3 * h * (C * σ₀ ^ 4 / σ ^ 4) := by ring
  have k1 : 8 / 3 * C * L ≤ ε := by nlinarith
  have k2 : 8 / 3 * (L * h ^ 2) * (C * σ₀ ^ 4 / σ ^ 4) ≤ ε := by
    have := mul_le_mul_of_nonneg_right hLh2 hc0
    rw [e2] at hD
    nlinarith
  rw [e1]
  have := mul_le_mul_of_nonneg_right k1 (sq_nonneg β)
  have := mul_le_mul_of_nonneg_right k2 (sq_nonneg z)
  linarith

lemma arith4 (C ε h β z σ₀ σ ζT : ℝ) (hC : 0 < C) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hD : 3 * C * σ₀ ^ 4 * h / σ ^ 4 ≤ ε) (hσ : 0 < σ) (hζ : 0 < ζT) (hζle : ζT ^ 2 ≤ σ₀ ^ 4) :
    4 / 3 * C * (2 * β ^ 2 + 2 * (σ₀ ^ 4 * h ^ 2 / σ ^ 4) * z ^ 2) ≤
      ε * z ^ 2 + 3 * C * σ₀ ^ 4 * (ζT ^ 2)⁻¹ * β ^ 2 := by
  have hc0 : 0 ≤ C * σ₀ ^ 4 / σ ^ 4 := by positivity
  have hge : 1 ≤ σ₀ ^ 4 * (ζT ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
  have e1 : 4 / 3 * C * (2 * β ^ 2 + 2 * (σ₀ ^ 4 * h ^ 2 / σ ^ 4) * z ^ 2)
      = (8 / 3 * C) * β ^ 2 + (8 / 3 * (h * h) * (C * σ₀ ^ 4 / σ ^ 4)) * z ^ 2 := by ring
  have e2 : 3 * C * σ₀ ^ 4 * h / σ ^ 4 = 3 * h * (C * σ₀ ^ 4 / σ ^ 4) := by ring
  have e3 : 3 * C * σ₀ ^ 4 * (ζT ^ 2)⁻¹ * β ^ 2 = (3 * C * β ^ 2) * (σ₀ ^ 4 * (ζT ^ 2)⁻¹) := by
    ring
  have hhh : h * h ≤ h := by nlinarith
  have k2 : 8 / 3 * (h * h) * (C * σ₀ ^ 4 / σ ^ 4) ≤ ε := by
    have := mul_le_mul_of_nonneg_right hhh hc0
    rw [e2] at hD
    nlinarith
  have k1 : 8 / 3 * C * β ^ 2 ≤ (3 * C * β ^ 2) * (σ₀ ^ 4 * (ζT ^ 2)⁻¹) := by
    have : 0 ≤ 3 * C * β ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hge this
    nlinarith [sq_nonneg β]
  rw [e1, e3]
  have := mul_le_mul_of_nonneg_right k2 (sq_nonneg z)
  linarith

lemma hRn_aux {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (C t t' β z L : ℝ) (htt' : t ≤ t')
    (hL : L = t' - t) (B : ℝ)
    (hpt : ∀ u, t ≤ u → u ≤ t' →
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β u ω) ^ 2)) ∂P)
        ≤ ENNReal.ofReal B) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (C * ∑ i ∈ Finset.range (n + 1),
      (t' - t) / (n + 1) * (betaZ M W z t β (t + i * ((t' - t) / (n + 1))) ω) ^ 2)) ∂P)
      ≤ ENNReal.ofReal B := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 1 / (n + 1) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  obtain ⟨ui, hui⟩ : ∃ ui : ℕ → ℝ, ui = fun i : ℕ => t + (i : ℝ) * ((t' - t) / (n + 1)) :=
    ⟨_, rfl⟩
  have hjensen : ∀ ω, ENNReal.ofReal (Real.exp (C * ∑ i ∈ Finset.range (n + 1),
      (t' - t) / (n + 1) * (betaZ M W z t β (t + i * ((t' - t) / (n + 1))) ω) ^ 2)) ≤
      ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal w *
        ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)) := by
    intro ω
    have hCR : C * ∑ i ∈ Finset.range (n + 1),
        (t' - t) / (n + 1) * (betaZ M W z t β (t + i * ((t' - t) / (n + 1))) ω) ^ 2
        = ∑ i ∈ Finset.range (n + 1),
          w • ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hw, hui, hL, smul_eq_mul]
      field_simp
    have hJ := (convexOn_exp).map_sum_le (t := Finset.range (n + 1)) (w := fun _ => w)
      (p := fun i => (C * L) * (betaZ M W z t β (ui i) ω) ^ 2)
      (fun _ _ => hw0) (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hw]; push_cast; field_simp) (fun _ _ => Set.mem_univ _)
    rw [hCR]
    calc ENNReal.ofReal (Real.exp (∑ i ∈ Finset.range (n + 1),
            w • ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)))
        ≤ ENNReal.ofReal (∑ i ∈ Finset.range (n + 1),
            w • Real.exp ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hJ
      _ = ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal w *
            ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_eq_mul, ENNReal.ofReal_mul hw0]
  calc _ ≤ ∫⁻ ω, ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal w *
          ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)) ∂P :=
        lintegral_mono hjensen
    _ = ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal w *
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β (ui i) ω) ^ 2)) ∂P := by
        rw [lintegral_finsetSum' _ (fun i _ =>
          (aem_exp M P W hW z t β (ui i) (C * L)).const_mul _)]
        apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal w * ENNReal.ofReal B := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        gcongr
        have hi' : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hi
        have hk : 0 ≤ (t' - t) / (n + 1) := div_nonneg (by linarith) hn1.le
        rw [hui]
        apply hpt
        · have : (0:ℝ) ≤ i * ((t' - t) / (n + 1)) := mul_nonneg (Nat.cast_nonneg _) hk
          linarith
        · have : (i : ℝ) * ((t' - t) / (n + 1)) ≤ t' - t := by
            rw [mul_div_assoc', div_le_iff₀ hn1]
            have : 0 ≤ t' - t := by linarith
            nlinarith
          linarith
    _ = ENNReal.ofReal B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
        have : ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal w = 1 := by
          rw [hw, ENNReal.ofReal_div_of_pos hn1, ENNReal.ofReal_one]
          have : ENNReal.ofReal ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl
          rw [this, ENNReal.mul_div_cancel (by simp) (by simp)]
        rw [this, one_mul]

lemma c4 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (C ε h : ℝ) (hC : 0 < C)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hA : 2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2) ≤ 1 / 4)
    (hD : 3 * C * M.σ₀ ^ 4 * h / M.σ ^ 4 ≤ ε) (t β z s : ℝ) (ht0 : 0 ≤ t) (hts : t ≤ s)
    (hd : s - t ≤ h) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (C * (betaZ M W z t β s ω) ^ 2)) ∂P)
      ≤ ENNReal.ofReal (Real.sqrt 2 *
          Real.exp (ε * z ^ 2 + 3 * C * M.σ₀ ^ 4 * (M.ζ M.T ^ 2)⁻¹ * β ^ 2)) := by
  obtain ⟨hlt, hle⟩ := bound M z t β s C h ht0 hts hd hC.le hA
  rw [key M P W hW z t β s C ht0 hts hlt]
  apply ENNReal.ofReal_le_ofReal
  refine hle.trans ?_
  have hsq2 : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  apply mul_le_mul hsq2 _ (by positivity) (by positivity)
  apply Real.exp_le_exp.2
  have hT := M.hT
  have hzT := zeta_pos M hT.le
  have hzTle := zeta_le M hT.le
  have hzsq : M.ζ M.T ^ 2 ≤ M.σ₀ ^ 4 := by
    have : M.ζ M.T ^ 2 ≤ (M.σ₀ ^ 2) ^ 2 := pow_le_pow_left₀ hzT.le hzTle 2
    simpa [← pow_mul] using this
  exact arith4 C ε h β z M.σ₀ M.σ (M.ζ M.T) hC hh0 hh1 hD M.hσ hzT hzsq

lemma c3 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) (C ε h : ℝ) (hC : 0 < C)
    (hh1 : h ≤ 1) (hA : 2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2) ≤ 1 / 4) (hB : 3 * C * h ≤ ε)
    (hD : 3 * C * M.σ₀ ^ 4 * h / M.σ ^ 4 ≤ ε) (t t' β z : ℝ) (ht0 : 0 ≤ t) (htt' : t < t')
    (ht'h : t' - t ≤ h) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (C * ∫ u in t..t', (betaZ M W z t β u ω) ^ 2)) ∂P)
      ≤ ENNReal.ofReal (4 / 3 * Real.exp (ε * (z ^ 2 + β ^ 2))) := by
  have hσ := M.hσ
  obtain ⟨L, hL⟩ : ∃ L, L = t' - t := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; linarith
  have hLh : L ≤ h := by rw [hL]; exact ht'h
  obtain ⟨B, hBdef⟩ : ∃ B, B = 4 / 3 * Real.exp (ε * (z ^ 2 + β ^ 2)) := ⟨_, rfl⟩
  rw [← hBdef]
  -- pointwise Gaussian bound at every `u ∈ [t, t']`
  have hpt : ∀ u, t ≤ u → u ≤ t' →
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((C * L) * (betaZ M W z t β u ω) ^ 2)) ∂P)
        ≤ ENNReal.ofReal B := by
    intro u htu hut
    have hd : u - t ≤ h := by linarith
    have hx : 2 * (C * L) * (M.σ₀ ^ 4 * h / M.σ ^ 2) ≤ 1 / 4 := by
      have e : 2 * (C * L) * (M.σ₀ ^ 4 * h / M.σ ^ 2)
          = L * (2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2)) := by ring
      rw [e]
      have hL1 : L ≤ 1 := hLh.trans hh1
      have h0 : 0 ≤ 2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2) := by
        have : 0 ≤ h := hL0.le.trans hLh
        positivity
      calc L * (2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2)) ≤ 1 * (2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2)) :=
            mul_le_mul_of_nonneg_right hL1 h0
        _ ≤ 1 / 4 := by rw [one_mul]; exact hA
    obtain ⟨hlt, hle⟩ := bound M z t β u (C * L) h ht0 htu hd (by positivity) hx
    rw [key M P W hW z t β u (C * L) ht0 htu hlt]
    apply ENNReal.ofReal_le_ofReal
    refine hle.trans ?_
    rw [hBdef]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.2
    exact arith3 C ε h L β z M.σ₀ M.σ hC hh1 hL0.le hLh hB hD hσ
  -- Riemann sums
  set R : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (n + 1),
    (t' - t) / (n + 1) * (betaZ M W z t β (t + i * ((t' - t) / (n + 1))) ω) ^ 2 with hR
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (Real.exp (C * R n ω))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (C * ∫ u in t..t', (betaZ M W z t β u ω) ^ 2)))) := by
    filter_upwards [hW.cont] with ω hω
    have hr := riemann (fun u => (betaZ M W z t β u ω) ^ 2) htt'
      (cont_beta M W z t β ω hω t t' ht0)
    have hc : Continuous (fun y : ℝ => ENNReal.ofReal (Real.exp (C * y))) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact (hc.tendsto _).comp hr
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (C * R n ω))) P := by
    intro n
    have : AEMeasurable (R n) P := by
      simp only [hR]
      refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
      exact ((aem_beta M P W hW z t β _).pow_const 2).const_mul _
    exact (by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (C * y))).comp_aemeasurable this
  have hRn : ∀ n, (∫⁻ ω, ENNReal.ofReal (Real.exp (C * R n ω)) ∂P) ≤ ENNReal.ofReal B := by
    intro n
    exact hRn_aux M P W hW C t t' β z L htt'.le hL B hpt n
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (C * ∫ u in t..t', (betaZ M W z t β u ω) ^ 2)) ∂P)
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Real.exp (C * R n ω))) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hconv] with ω hω
        exact hω.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (C * R n ω)) ∂P) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal B :=
        Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hRn)

end SmoothAmbC1Aux

open SmoothAmbEq.Gaussian SmoothAmbC1Aux

theorem solution (M : Model) :
    ∀ C > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ h > (0 : ℝ),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : ℝ≥0 → Ω → ℝ), IsBrownianReal W P →
      ∀ t ∈ Ico 0 M.T, ∀ β z : ℝ,
        (∫⁻ ω, ENNReal.ofReal
            (Real.exp (C * ∫ u in t..min (t + h) M.T, (betaZ M W z t β u ω) ^ 2)) ∂P)
          ≤ ENNReal.ofReal (4 / 3 * Real.exp (ε * (z ^ 2 + β ^ 2))) ∧
        ∀ s ∈ Ico t (min (t + h) M.T),
          (∫⁻ ω, ENNReal.ofReal (Real.exp (C * (betaZ M W z t β s ω) ^ 2)) ∂P)
            ≤ ENNReal.ofReal (Real.sqrt 2 *
                Real.exp (ε * z ^ 2 + 3 * C * M.σ₀ ^ 4 * (M.ζ M.T ^ 2)⁻¹ * β ^ 2)) := by
  intro C hC ε hε
  have hσ := M.hσ; have hσ₀ := M.hσ₀
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℝ, a1 = 8 * C * M.σ₀ ^ 4 / M.σ ^ 2 := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℝ, a2 = 3 * C / ε := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a3 : ℝ, a3 = 3 * C * M.σ₀ ^ 4 / (M.σ ^ 4 * ε) := ⟨_, rfl⟩
  have ha1' : 0 ≤ a1 := by rw [ha1]; positivity
  have ha2' : 0 ≤ a2 := by rw [ha2]; positivity
  have ha3' : 0 ≤ a3 := by rw [ha3]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 + a1 + a2 + a3 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK]; linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / K := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hKh : h * K = 1 := by rw [hh]; field_simp
  have hh1 : h ≤ 1 := by
    have : h * 1 ≤ h * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith) hh0.le
    linarith
  have hA : 2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2) ≤ 1 / 4 := by
    have e : 2 * C * (M.σ₀ ^ 4 * h / M.σ ^ 2) = h * a1 / 4 := by rw [ha1]; field_simp; ring
    have : h * a1 ≤ h * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith) hh0.le
    rw [e]; linarith
  have hB : 3 * C * h ≤ ε := by
    have e : 3 * C * h = ε * (h * a2) := by rw [ha2]; field_simp
    have : h * a2 ≤ h * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith) hh0.le
    rw [e]; nlinarith
  have hD : 3 * C * M.σ₀ ^ 4 * h / M.σ ^ 4 ≤ ε := by
    have e : 3 * C * M.σ₀ ^ 4 * h / M.σ ^ 4 = ε * (h * a3) := by rw [ha3]; field_simp
    have : h * a3 ≤ h * K := mul_le_mul_of_nonneg_left (by rw [hK]; linarith) hh0.le
    rw [e]; nlinarith
  refine ⟨h, hh0, ?_⟩
  intro Ω _ P _ W hW t ht β z
  have ht0 : 0 ≤ t := ht.1
  have htt' : t < min (t + h) M.T := lt_min (by linarith) ht.2
  have ht'h : min (t + h) M.T - t ≤ h := by have := min_le_left (t + h) M.T; linarith
  refine ⟨c3 M P W hW C ε h hC hh1 hA hB hD t _ β z ht0 htt' ht'h, ?_⟩
  intro s hs
  exact c4 M P W hW C ε h hC hh0.le hh1 hA hD t β z s ht0 hs.1 (by linarith [hs.2])
