-- Prove2me | solution 1 for RoughSurfaceScattering.analyticAt_of_iteratedFDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T06:03:05.913242+00:00
-- url     : https://prove2.me/submissions/590133bc-3a6b-42ec-bf8c-5e4ce1ece33e

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory Filter Topology Nat
open RoughSurfaceScattering

theorem solution {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (x : E) (R M ρ : ℝ) (hR : 0 < R) (hρ : 0 < ρ)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Metric.ball x R))
    (hb : ∀ n : ℕ, ∀ y ∈ Metric.ball x R,
      ‖iteratedFDeriv ℝ n f y‖ ≤ M * (n.factorial : ℝ) / ρ ^ n) :
    AnalyticAt ℝ f x := by
  have hM : 0 ≤ M := by
    have := hb 0 x (Metric.mem_ball_self hR)
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, pow_zero, div_one] at this
    exact (norm_nonneg _).trans this
  -- the Taylor series at `x`
  set p : FormalMultilinearSeries ℝ E F := fun n => ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n f x
    with hp
  have hpn : ∀ n, ‖p n‖ ≤ M / ρ ^ n := by
    intro n
    have hfact : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
    calc ‖p n‖ = (n ! : ℝ)⁻¹ * ‖iteratedFDeriv ℝ n f x‖ := by
          rw [hp, norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ (n ! : ℝ)⁻¹ * (M * n ! / ρ ^ n) :=
          mul_le_mul_of_nonneg_left (hb n x (Metric.mem_ball_self hR)) (by positivity)
      _ = M / ρ ^ n := by field_simp
  set r : ℝ := min R (ρ / 2) with hr
  have hrpos : 0 < r := lt_min hR (by positivity)
  refine ⟨p, ENNReal.ofReal r, ?_⟩
  refine ⟨?_, by simpa using hrpos, ?_⟩
  · -- radius
    have hc : ((Real.toNNReal (ρ / 2) : NNReal) : ℝ) = ρ / 2 :=
      Real.coe_toNNReal _ (by positivity)
    have hle := p.le_radius_of_bound M (r := Real.toNNReal (ρ / 2)) fun n => by
      rw [hc]
      have h1 := mul_le_mul_of_nonneg_right (hpn n) (by positivity : (0 : ℝ) ≤ (ρ / 2) ^ n)
      refine h1.trans ?_
      have : M / ρ ^ n * (ρ / 2) ^ n = M * (1 / 2) ^ n := by
        rw [div_pow, div_pow, one_pow]
        have : ρ ^ n ≠ 0 := by positivity
        field_simp
      rw [this]
      exact mul_le_of_le_one_right hM (pow_le_one₀ (by norm_num) (by norm_num))
    refine le_trans ?_ hle
    exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  · -- convergence to `f (x + y)`
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mp hy
    set q := ‖y‖ / ρ with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      rw [hq, div_lt_one hρ]
      have := min_le_right R (ρ / 2); linarith
    have hyR : ‖y‖ < R := lt_of_lt_of_le hy' (min_le_left _ _)
    have hterm : ∀ n, ‖p n (fun _ => y)‖ ≤ M * q ^ n := by
      intro n
      calc ‖p n (fun _ => y)‖ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := (p n).le_opNorm _
        _ = ‖p n‖ * ‖y‖ ^ n := by simp
        _ ≤ M / ρ ^ n * ‖y‖ ^ n := mul_le_mul_of_nonneg_right (hpn n) (by positivity)
        _ = M * q ^ n := by rw [hq, div_pow]; ring
    have hsumm : Summable fun n => ‖p n (fun _ => y)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left M)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsumm]
    rw [← tendsto_add_atTop_iff_nat 1]
    -- Taylor's formula with integral remainder
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • y ∈ Metric.ball x R := by
      intro t ht
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg ht.1]
      calc t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ < R := by linarith
    have htaylor : ∀ n : ℕ, f (x + y) = ∑ k ∈ Finset.range (n + 1), p k (fun _ => y) +
        (n ! : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1,
          (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y) := by
      intro n
      have := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y) (n := n)
        fun t ht => ((hf (n + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht)))
      rw [this]
      congr 1
    -- the remainder tends to zero
    have hrem : ∀ n : ℕ, ‖f (x + y) - ∑ k ∈ Finset.range (n + 1), p k (fun _ => y)‖ ≤
        M * ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) := by
      intro n
      rw [htaylor n, add_sub_cancel_left, norm_smul]
      have hfact : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
      have hint : ‖∫ t in (0 : ℝ)..1,
          (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤
          M * ((n + 1) ! : ℝ) / ρ ^ (n + 1) * ‖y‖ ^ (n + 1) * |1 - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
        rw [Set.uIoc_of_le zero_le_one] at ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        rw [norm_smul]
        have h1 : ‖(1 - t) ^ n‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (by linarith [ht'.2])]
          exact pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1])
        have h2 : ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖ ≤
            M * ((n + 1) ! : ℝ) / ρ ^ (n + 1) * ‖y‖ ^ (n + 1) := by
          calc _ ≤ ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ∏ _i : Fin (n + 1), ‖y‖ :=
                ContinuousMultilinearMap.le_opNorm _ _
            _ = ‖iteratedFDeriv ℝ (n + 1) f (x + t • y)‖ * ‖y‖ ^ (n + 1) := by simp
            _ ≤ _ := mul_le_mul_of_nonneg_right (hb (n + 1) _ (hseg t ht')) (by positivity)
        calc ‖(1 - t) ^ n‖ * ‖iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
            ≤ 1 * (M * ((n + 1) ! : ℝ) / ρ ^ (n + 1) * ‖y‖ ^ (n + 1)) :=
              mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      calc ‖((n ! : ℝ)⁻¹)‖ * ‖∫ t in (0 : ℝ)..1,
            (1 - t) ^ n • iteratedFDeriv ℝ (n + 1) f (x + t • y) (fun _ => y)‖
          ≤ (n ! : ℝ)⁻¹ * (M * ((n + 1) ! : ℝ) / ρ ^ (n + 1) * ‖y‖ ^ (n + 1) * |1 - 0|) := by
            rw [Real.norm_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_left hint (by positivity)
        _ = M * ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) := by
            rw [hq, div_pow, Nat.factorial_succ]
            push_cast
            simp only [sub_zero, abs_one, mul_one]
            field_simp
    have hlim : Tendsto (fun n : ℕ => M * ((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) atTop (𝓝 0) := by
      have h := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      have h' := h.const_mul M
      simp only [mul_zero] at h'
      refine h'.congr fun n => ?_
      simp only [Function.comp_apply]
      ring
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [norm_sub_rev]
    simpa [hp] using hrem n
