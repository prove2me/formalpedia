-- Prove2me | solution 1 for SamplingIPM.Spectra.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T06:57:30.368215+00:00
-- url     : https://prove2.me/submissions/6624b3ab-6d35-4f7d-bd00-612477a976ab

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

set_option autoImplicit false

open scoped RealInnerProductSpace ENNReal
open MeasureTheory Filter Topology Metric

namespace TS31

open EntropicBarrier.Universal

theorem volume_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K :=
  (isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset)

theorem Z_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : 0 < ∫ x in K, Real.exp ⟪θ, x⟫ := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫) := by
    fun_prop
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (hc.continuousOn.integrableOn_compact hK.1)]
  have : Function.support (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫) =
      Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [this, Measure.restrict_apply_univ]
  exact volume_pos hK

theorem isProb {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : IsProbabilityMeasure (expFamily K θ) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (⟪θ, x⟫ - logPartition K θ)) := by fun_prop
  have hfin : IsFiniteMeasure (expFamily K θ) := by
    unfold expFamily
    exact isFiniteMeasure_withDensity_ofReal
      (hc.continuousOn.integrableOn_compact hK.1).hasFiniteIntegral
  have h1 : ∫ x, (1 : ℝ) ∂(expFamily K θ) = 1 := by
    unfold expFamily
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have : ∀ x : EuclideanSpace ℝ (Fin n),
        (ENNReal.ofReal (Real.exp (⟪θ, x⟫ - logPartition K θ))).toReal • (1 : ℝ) =
          (Real.exp (logPartition K θ))⁻¹ * Real.exp ⟪θ, x⟫ := by
      intro x
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_one, Real.exp_sub]
      ring
    simp_rw [this]
    rw [integral_const_mul]
    unfold logPartition
    rw [Real.exp_log (Z_pos hK θ), inv_mul_cancel₀ (Z_pos hK θ).ne']
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  refine ⟨?_⟩
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_one_iff _).1 h1

theorem expFamily_apply {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (B : Set (EuclideanSpace ℝ (Fin n))) (hB : B ⊆ K) :
    expFamily K θ B =
      ∫⁻ x in B, ENNReal.ofReal (Real.exp (⟪θ, x⟫ - logPartition K θ)) := by
  unfold expFamily
  rw [withDensity_apply' _ B, Measure.restrict_restrict' hK.1.measurableSet,
    Set.inter_eq_left.2 hB]

theorem expFamily_compl {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : expFamily K θ Kᶜ = 0 := by
  unfold expFamily
  rw [withDensity_apply _ hK.1.measurableSet.compl,
    Measure.restrict_restrict hK.1.measurableSet.compl, Set.compl_inter_self,
    Measure.restrict_empty, lintegral_zero_measure]

/-- The homothety `x ↦ (1-ε)x + εp` toward a point `p ∈ K` loses at most the factor
`(1-ε)^n e^{-2εR‖θ‖}` of `p_θ`-mass. -/
theorem image_ge {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (y₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hout : K ⊆ closedBall y₀ R)
    (θ p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ K) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : B ⊆ K) (hBm : MeasurableSet B) :
    ENNReal.ofReal ((1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖))) * expFamily K θ B ≤
      expFamily K θ ((fun x => (1 - ε) • x + ε • p) '' B) := by
  set H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => (1 - ε) • x + ε • p with hH
  have hHK : H '' B ⊆ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hK.2.1 (hB hx) hp (by linarith) hε0.le (by ring)
  rw [expFamily_apply hK θ B hB, expFamily_apply hK θ _ hHK]
  have hf' : ∀ x ∈ B, HasFDerivWithinAt H
      ((1 - ε) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) B x := by
    intro x _
    exact (((hasFDerivAt_id x).const_smul (1 - ε)).add_const (ε • p)).hasFDerivWithinAt
  have hinj : Set.InjOn H B := by
    intro x _ y _ hxy
    have h1 : (1 - ε) • x = (1 - ε) • y := add_right_cancel hxy
    exact smul_right_injective _ (by linarith : (1 - ε) ≠ 0) h1
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBm hf' hinj]
  have hdet : ((1 - ε) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).det =
      (1 - ε) ^ n := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, ContinuousLinearMap.coe_id,
      LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin, mul_one]
  rw [hdet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hBm (fun x hx => ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_nonneg (pow_nonneg (by linarith) n), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) n)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hx' := hout (hB hx)
  have hp' := hout hp
  rw [mem_closedBall] at hx' hp'
  have hd : ‖p - x‖ ≤ 2 * R := by
    have := dist_triangle p y₀ x
    rw [dist_comm y₀ x, dist_eq_norm] at this
    linarith
  have hin : -(‖θ‖ * ‖p - x‖) ≤ ⟪θ, p - x⟫ := by
    have := abs_real_inner_le_norm θ (p - x)
    linarith [neg_abs_le ⟪θ, p - x⟫]
  have hexp : ⟪θ, H x⟫ = ⟪θ, x⟫ + ε * ⟪θ, p - x⟫ := by
    simp only [hH, inner_add_right, inner_smul_right, inner_sub_right]
    ring
  rw [hexp]
  have : ε * (‖θ‖ * ‖p - x‖) ≤ ε * (‖θ‖ * (2 * R)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) hε0.le
  nlinarith [mul_le_mul_of_nonneg_left hin hε0.le]

theorem covForm_nonneg {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ v : EuclideanSpace ℝ (Fin n)) : 0 ≤ covForm K θ v v := by
  unfold covForm
  exact integral_nonneg fun x => mul_self_nonneg _

/-- The core estimate: `δ² q ≤ (1 + q) Σ(θ)[v,v]`. -/
theorem main {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r R : ℝ) (hr : 0 < r)
    (hin : ball x₀ r ⊆ K) (hout : K ⊆ closedBall y₀ R) (θ v : EuclideanSpace ℝ (Fin n))
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 ≤ δ)
    (hδ : (2 - ε) * δ ≤ ε * (r * ‖v‖)) :
    δ ^ 2 * ((1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖))) ≤
      (1 + (1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖))) * covForm K θ v v := by
  set q := (1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖)) with hq
  have hq0 : 0 ≤ q := mul_nonneg (pow_nonneg (by linarith) n) (Real.exp_pos _).le
  haveI := isProb hK θ
  set ν := expFamily K θ with hν
  set m := meanMap K θ
  set W : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪x - m, v⟫ with hW
  have hWc : Continuous W := by fun_prop
  set A : Set (EuclideanSpace ℝ (Fin n)) := {x | |W x| < δ} with hA
  have hAm : MeasurableSet A := (isOpen_lt (by fun_prop) continuous_const).measurableSet
  -- Step 1: the variance dominates `δ² ν(Aᶜ)`.
  have hae : ∀ᵐ x ∂ν, x ∈ K := by
    rw [hν]; unfold expFamily
    exact Measure.AbsolutelyContinuous.ae_le (withDensity_absolutelyContinuous _ _)
      (ae_restrict_mem hK.1.measurableSet)
  have hfc : Continuous (fun x => W x * W x) := by fun_prop
  obtain ⟨C, hC⟩ := hK.1.exists_bound_of_continuousOn hfc.continuousOn
  have hfi : Integrable (fun x => W x * W x) ν :=
    memLp_one_iff_integrable.1
      (MemLp.of_bound hfc.aestronglyMeasurable C (hae.mono fun x hx => hC x hx))
  have h1 : δ ^ 2 * ν.real Aᶜ ≤ covForm K θ v v := by
    have hcov : covForm K θ v v = ∫ x, W x * W x ∂ν := rfl
    rw [hcov]
    calc δ ^ 2 * ν.real Aᶜ = ∫ x, Aᶜ.indicator (fun _ => δ ^ 2) x ∂ν := by
          rw [integral_indicator_const _ hAm.compl, smul_eq_mul, mul_comm]
      _ ≤ ∫ x, W x * W x ∂ν := by
          refine integral_mono ((integrable_const _).indicator hAm.compl) hfi (fun x => ?_)
          by_cases hx : x ∈ Aᶜ
          · rw [Set.indicator_of_mem hx]
            have : δ ≤ |W x| := by
              simpa [hA] using hx
            have h2 : δ ^ 2 ≤ |W x| ^ 2 := pow_le_pow_left₀ hδ0 this 2
            rw [sq_abs] at h2
            nlinarith
          · rw [Set.indicator_of_notMem hx]
            exact mul_self_nonneg _
  -- Step 2: `(1 + q) ν(A) ≤ 1` via the homothety.
  set σ : ℝ := if 0 ≤ W x₀ then 1 else -1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hσW : 0 ≤ σ * W x₀ := by
    rw [hσ]; split_ifs with h
    · simpa using h
    · simp only [neg_mul, one_mul, neg_nonneg]; linarith [not_le.1 h]
  set p := x₀ + (σ * r / ‖v‖) • v with hp
  have hpK : p ∈ K := by
    have hcb : closedBall x₀ r ⊆ K := by
      rw [← closure_ball x₀ hr.ne']
      exact closure_minimal hin hK.1.isClosed
    apply hcb
    rw [mem_closedBall, dist_eq_norm, hp, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_div, abs_mul, hσ1, one_mul, abs_of_pos hr, abs_norm]
    rcases eq_or_ne ‖v‖ 0 with h0 | h0
    · rw [h0, div_zero, zero_mul]; exact hr.le
    · rw [div_mul_cancel₀ _ h0]
  have hσp : r * ‖v‖ ≤ σ * W p := by
    have : W p = W x₀ + σ * r * (‖v‖ ^ 2 / ‖v‖) := by
      simp only [hW, hp]
      rw [add_sub_right_comm, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      ring
    have hvv : ‖v‖ ^ 2 / ‖v‖ = ‖v‖ := by
      rcases eq_or_ne ‖v‖ 0 with h0 | h0
      · rw [h0]; simp
      · field_simp
    rw [this, hvv, mul_add]
    have hσσ : σ * σ = 1 := by
      have := hσ1; rw [← abs_mul_abs_self σ, this, one_mul]
    have e2 : σ * (σ * r * ‖v‖) = r * ‖v‖ := by
      rw [← mul_assoc, ← mul_assoc, hσσ, one_mul]
    rw [e2]; linarith
  set B := A ∩ K with hBdef
  have hBm : MeasurableSet B := hAm.inter hK.1.measurableSet
  have himg := image_ge hK y₀ R hout θ p hpK ε hε0 hε1 B Set.inter_subset_right hBm
  set HB := (fun x => (1 - ε) • x + ε • p) '' B with hHB
  have hdisj : Disjoint HB A := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, ⟨hxA, hxK⟩, rfl⟩ hyA
    have hxA' : |W x| < δ := hxA
    have hyA' : |W ((1 - ε) • x + ε • p)| < δ := hyA
    have hlin : W ((1 - ε) • x + ε • p) = (1 - ε) * W x + ε * W p := by
      simp only [hW, inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    rw [hlin] at hyA'
    have hσx : -δ < σ * W x := by
      have := neg_abs_le (σ * W x)
      rw [abs_mul, hσ1, one_mul] at this
      linarith
    have hsum : δ < σ * ((1 - ε) * W x + ε * W p) := by
      have e1 : σ * ((1 - ε) * W x + ε * W p) = (1 - ε) * (σ * W x) + ε * (σ * W p) := by
        ring
      rw [e1]
      have := mul_lt_mul_of_pos_left hσx (by linarith : (0 : ℝ) < 1 - ε)
      have := mul_le_mul_of_nonneg_left hσp hε0.le
      nlinarith
    have := le_abs_self (σ * ((1 - ε) * W x + ε * W p))
    rw [abs_mul, hσ1, one_mul] at this
    linarith
  have hAeq : ν B = ν A := by
    rw [hBdef]
    exact measure_inter_conull (expFamily_compl hK θ)
  have h2 : ENNReal.ofReal q * ν A + ν A ≤ 1 := by
    calc ENNReal.ofReal q * ν A + ν A ≤ ν HB + ν A := by
          rw [← hAeq]; exact add_le_add himg le_rfl
      _ = ν (HB ∪ A) := (measure_union hdisj hAm).symm
      _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have h2r : (1 + q) * ν.real A ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top h2
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (measure_ne_top _ _), ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0,
      ENNReal.toReal_one] at this
    rw [measureReal_def]
    linarith
  have h3 : ν.real Aᶜ = 1 - ν.real A := by
    rw [measureReal_compl hAm, probReal_univ]
  rw [h3] at h1
  have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + q),
    mul_le_mul_of_nonneg_left h2r hδ2]

/-- `(n/(n+2))^n ≥ e^{-2}`. -/
theorem pow_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-2) ≤ (1 - 2 / ((n : ℝ) + 2)) ^ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 - 2 / ((n : ℝ) + 2) = (1 + 2 / (n : ℝ))⁻¹ := by
    field_simp; ring
  have h2 : Real.exp (-(2 / (n : ℝ))) ≤ 1 - 2 / ((n : ℝ) + 2) := by
    rw [h1, Real.exp_neg]
    apply inv_anti₀ (by positivity)
    have := Real.add_one_le_exp (2 / (n : ℝ))
    linarith
  calc Real.exp (-2) = Real.exp (-(2 / (n : ℝ))) ^ n := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le h2 n

theorem exp_const : 1 ≤ 15 * (Real.exp (-2) * Real.exp (-(1 / 2))) := by
  rw [← Real.exp_add]
  have h : Real.exp (5 / 2) ≤ 15 := by
    have he := Real.exp_one_lt_d9
    have h5 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
    have hpos := Real.exp_pos (5 / 2)
    have : Real.exp 1 ^ 5 < 225 := by
      calc Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
            pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
        _ < 225 := by norm_num
    nlinarith
  have : Real.exp (-2 + -(1 / 2)) = (Real.exp (5 / 2))⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  rw [this]
  rw [le_mul_inv_iff₀ (Real.exp_pos _)]
  linarith

end TS31

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r R ϑ : ℝ) (hr : 0 < r)
    (hin : Metric.ball x₀ r ⊆ K) (hout : K ⊆ Metric.closedBall y₀ R)
    (hϑ0 : 0 ≤ ϑ) (hϑ : SatisfiesNuBound K (entropicBarrier K) ϑ)
    (θ : EuclideanSpace ℝ (Fin n)) :
    (‖θ‖ ≤ 1 / (4 * R) →
      ∀ v : EuclideanSpace ℝ (Fin n),
        (1 / 16) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2 ≤ covForm K θ v v) ∧
    (1 / (4 * R) < ‖θ‖ →
      ∀ v : EuclideanSpace ℝ (Fin n),
        (1 / 64) * (1 / (4 * R * ‖θ‖)) ^ (4 * Real.sqrt ϑ + 2) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2
          ≤ covForm K θ v v) := by
  have hR : 0 ≤ R := by
    have hx := hout (hin (Metric.mem_ball_self hr))
    rw [Metric.mem_closedBall] at hx
    exact dist_nonneg.trans hx
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    have hv : ∀ v : EuclideanSpace ℝ (Fin 0), ‖v‖ = 0 := fun v => by
      rw [Subsingleton.elim v 0, norm_zero]
    refine ⟨fun _ v => ?_, fun _ v => ?_⟩ <;>
      · rw [hv v]; simpa using TS31.covForm_nonneg K θ v
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hq15 : ∀ q : ℝ, Real.exp (-2) * Real.exp (-(1 / 2)) ≤ q →
      ∀ δ C : ℝ, δ ^ 2 * q ≤ (1 + q) * C → δ ^ 2 / 16 ≤ C := by
    intro q hq δ C h
    have h15 := TS31.exp_const
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
    have h16 : 1 + q ≤ 16 * q := by linarith
    have hd := sq_nonneg δ
    have : δ ^ 2 * (1 + q) ≤ δ ^ 2 * (16 * q) := mul_le_mul_of_nonneg_left h16 hd
    nlinarith
  refine ⟨fun hθ v => ?_, fun hθ v => ?_⟩
  · -- small θ: ε = 2/(n+2), δ = r‖v‖/(n+1)
    set ε : ℝ := 2 / ((n : ℝ) + 2) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε < 1 := by rw [hε, div_lt_one (by positivity)]; linarith
    set δ : ℝ := r * ‖v‖ / ((n : ℝ) + 1) with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hδc : (2 - ε) * δ ≤ ε * (r * ‖v‖) := by
      rw [hε, hδ]
      have : (2 - 2 / ((n : ℝ) + 2)) * (r * ‖v‖ / ((n : ℝ) + 1)) =
          2 / ((n : ℝ) + 2) * (r * ‖v‖) := by
        field_simp; ring
      rw [this]
    have hmain := TS31.main hK x₀ y₀ r R hr hin hout θ v ε δ hε0 hε1 hδ0 hδc
    have hRθ : R * ‖θ‖ ≤ 1 / 4 := by
      rcases hR.eq_or_lt with h0 | hpos
      · rw [← h0]; norm_num
      · rw [le_div_iff₀ (by positivity)] at hθ
        nlinarith
    have hq : Real.exp (-2) * Real.exp (-(1 / 2)) ≤
        (1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖)) := by
      apply mul_le_mul (TS31.pow_lower n hn1) _ (Real.exp_pos _).le
        (pow_nonneg (by linarith) n)
      apply Real.exp_le_exp.2
      have : 2 * ε * R * ‖θ‖ ≤ 2 * 1 * (1 / 4) := by
        rw [mul_assoc]
        exact mul_le_mul (by linarith) hRθ (by positivity) (by norm_num)
      linarith
    have := hq15 _ hq δ _ hmain
    have e : (1 / 16) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2 = δ ^ 2 / 16 := by
      rw [hδ]; ring
    rw [e]; exact this
  · -- large θ: τ = 4R‖θ‖ > 1, ε = 2/((n+2)τ), δ = εr‖v‖/2
    have hRpos : 0 < R := by
      rcases hR.eq_or_lt with h0 | hpos
      · exfalso
        have h1 := TS31.volume_pos hK
        rw [← h0] at hout
        have h2 : volume K ≤ 0 := by
          calc volume K ≤ volume (closedBall y₀ 0) := measure_mono hout
            _ = 0 := by
              rw [Measure.addHaar_closedBall _ _ le_rfl, finrank_euclideanSpace_fin,
                zero_pow hn1.ne', ENNReal.ofReal_zero, zero_mul]
        exact absurd (h1.trans_le h2) (lt_irrefl 0)
      · exact hpos
    set τ : ℝ := 4 * R * ‖θ‖ with hτ
    have hτ1 : 1 < τ := by
      rw [div_lt_iff₀ (by positivity)] at hθ
      rw [hτ]; linarith
    have hτ0 : 0 < τ := by linarith
    set ε : ℝ := 2 / (((n : ℝ) + 2) * τ) with hε
    have hε0 : 0 < ε := by positivity
    have hεle : ε ≤ 2 / ((n : ℝ) + 2) := by
      rw [hε]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have hε1 : ε < 1 := by
      have : 2 / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
      linarith
    set δ : ℝ := ε * (r * ‖v‖) / 2 with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hδc : (2 - ε) * δ ≤ ε * (r * ‖v‖) := by
      rw [hδ]
      have : 0 ≤ ε * (r * ‖v‖) := by positivity
      nlinarith
    have hmain := TS31.main hK x₀ y₀ r R hr hin hout θ v ε δ hε0 hε1 hδ0 hδc
    have hq : Real.exp (-2) * Real.exp (-(1 / 2)) ≤
        (1 - ε) ^ n * Real.exp (-(2 * ε * R * ‖θ‖)) := by
      apply mul_le_mul _ _ (Real.exp_pos _).le (pow_nonneg (by linarith) n)
      · exact (TS31.pow_lower n hn1).trans
          (pow_le_pow_left₀ (by
            have : 2 / ((n : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
            linarith) (by linarith) n)
      · apply Real.exp_le_exp.2
        have : 2 * ε * R * ‖θ‖ = 1 / ((n : ℝ) + 2) := by
          have hθ0 : ‖θ‖ ≠ 0 := by
            intro h; rw [hτ, h, mul_zero] at hτ0; exact lt_irrefl 0 hτ0
          rw [hε, hτ]; field_simp
          ring
        rw [this]
        have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith
        linarith
    have hC := hq15 _ hq δ _ hmain
    refine le_trans ?_ hC
    have hpow : (1 / τ) ^ (4 * Real.sqrt ϑ + 2) ≤ (1 / τ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge (by positivity)
        (by rw [div_le_one hτ0]; linarith)
      push_cast
      linarith [Real.sqrt_nonneg ϑ]
    have hδe : δ = r * ‖v‖ / (((n : ℝ) + 2) * τ) := by
      rw [hδ, hε]; field_simp
    have hA : 0 ≤ (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2 := by positivity
    calc 1 / 64 * (1 / τ) ^ (4 * Real.sqrt ϑ + 2) * (r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2
        = 1 / 64 * (1 / τ) ^ (4 * Real.sqrt ϑ + 2) * ((r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2) := by
          ring
      _ ≤ 1 / 64 * (1 / τ) ^ (2 : ℕ) * ((r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2) := by
          gcongr
      _ ≤ δ ^ 2 / 16 := by
          rw [hδe]
          have h2 : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
          have hn1' : ((n : ℝ) + 1) ≠ 0 := by positivity
          have hn2' : ((n : ℝ) + 2) ≠ 0 := by positivity
          have hτ' : τ ≠ 0 := hτ0.ne'
          have key : (r * ‖v‖ / (((n : ℝ) + 2) * τ)) ^ 2 / 16 -
              1 / 64 * (1 / τ) ^ (2 : ℕ) * ((r / ((n : ℝ) + 1)) ^ 2 * ‖v‖ ^ 2) =
              (r * ‖v‖) ^ 2 * (4 * ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 2) ^ 2) /
                (64 * τ ^ 2 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
            field_simp; ring
          have : 0 ≤ (r * ‖v‖) ^ 2 * (4 * ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 2) ^ 2) /
                (64 * τ ^ 2 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2) :=
            div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)
          linarith
