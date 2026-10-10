-- Prove2me | solution 1 for RealAnalytic.analyticAt_of_multiDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T19:47:23.017808+00:00
-- url     : https://prove2.me/submissions/d2aadce9-fa46-4427-80a2-a18369e0454e

import Theorems.Thm_RealAnalytic_norm_iteratedFDeriv_le_of_multiDeriv_bound
import Theorems.Thm_RealAnalytic_taylor_remainder_bound
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped ContDiff Topology NNReal ENNReal
open Filter
set_option autoImplicit false

theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r C A : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hA : 0 < A)
    (hu : ContDiffOn ℝ ∞ u (Metric.ball x r))
    (hbound : ∀ y ∈ Metric.ball x r, ∀ (α : Fin n → ℕ) (k : ℕ),
      ∑ i, α i = k → 1 ≤ k →
      |HunterPDE.Shared.multiDeriv u α y| ≤ C * A ^ k * (k.factorial : ℝ)) :
    AnalyticAt ℝ u x := by
  classical
  let B : ℝ := (n + 1) * A
  have hB : 0 < B := by dsimp [B]; positivity
  have hderiv : ∀ y ∈ Metric.ball x r, ∀ k : ℕ, 1 ≤ k →
      ‖iteratedFDeriv ℝ k u y‖ ≤ C * B ^ k * (k.factorial : ℝ) := by
    intro y hy k hk
    have hb := RealAnalytic.norm_iteratedFDeriv_le_of_multiDeriv_bound
      Metric.isOpen_ball hu hy hk (by positivity : 0 ≤ C * A ^ k * (k.factorial : ℝ))
      (fun α hα => hbound y hy α k hα hk)
    calc
      _ ≤ (n + 1 : ℝ) ^ k * (C * A ^ k * (k.factorial : ℝ)) := hb
      _ = C * B ^ k * (k.factorial : ℝ) := by dsimp [B]; rw [mul_pow]; ring
  let p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) ℝ :=
    fun k => (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k u x
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hp : ∀ k : ℕ, 1 ≤ k → ‖p k‖ ≤ C * B ^ k := by
    intro k hk
    have hf : 0 < (k.factorial : ℝ) := by positivity
    calc
      ‖p k‖ = (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k u x‖ := by
        simp [p, norm_smul]
      _ ≤ (k.factorial : ℝ)⁻¹ * (C * B ^ k * (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hderiv x hx k hk) (inv_nonneg.mpr hf.le)
      _ = C * B ^ k := by field_simp
  let ρ : ℝ≥0 := ⟨min r B⁻¹, le_of_lt (lt_min hr (inv_pos.mpr hB))⟩
  have hρ : 0 < (ρ : ℝ) := lt_min hr (inv_pos.mpr hB)
  have hρr : (ρ : ℝ) ≤ r := min_le_left _ _
  have hρB : B * (ρ : ℝ) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (min_le_right r B⁻¹) hB.le
    change B * min r B⁻¹ ≤ 1
    simpa only [mul_inv_cancel₀ hB.ne'] using this
  have hrad : (ρ : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound (max ‖p 0‖ C)
    intro k
    cases k with
    | zero => simp
    | succ k =>
      calc
        ‖p (k + 1)‖ * (ρ : ℝ) ^ (k + 1) ≤
          (C * B ^ (k + 1)) * (ρ : ℝ) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hp _ (by omega)) (pow_nonneg ρ.coe_nonneg _)
        _ = C * (B * (ρ : ℝ)) ^ (k + 1) := by
          have hBA : B = (n : ℝ) * A + A := by dsimp [B]; ring
          rw [hBA, pow_succ, mul_pow]
          ring
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (mul_nonneg hB.le ρ.coe_nonneg) hρB) hC
        _ ≤ max ‖p 0‖ C := by simp
  refine ⟨p, ρ, hrad, ?_, ?_⟩
  · exact_mod_cast hρ
  · intro h hh
    have hhρ : ‖h‖ < (ρ : ℝ) := by simpa using hh
    have hhr : ‖h‖ < r := hhρ.trans_le hρr
    have hq0 : 0 ≤ B * ‖h‖ := mul_nonneg hB.le (norm_nonneg _)
    have hq1 : B * ‖h‖ < 1 :=
      (mul_lt_mul_of_pos_left hhρ hB).trans_le hρB
    have hrem : ∀ᶠ k : ℕ in atTop,
        ‖u (x + h) - ∑ j ∈ Finset.range k, p j (fun _ => h)‖ ≤
          C * (B * ‖h‖) ^ k := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hb := RealAnalytic.taylor_remainder_bound hr hu hhr hk
        (by positivity : 0 ≤ C * B ^ k * (k.factorial : ℝ))
        (fun y hy => hderiv y hy k hk)
      have hf : (k.factorial : ℝ) ≠ 0 := by positivity
      calc
        _ ≤ (C * B ^ k * (k.factorial : ℝ)) / (k.factorial : ℝ) * ‖h‖ ^ k := hb
        _ = C * (B * ‖h‖) ^ k := by dsimp [B]; simp only [mul_pow]; field_simp
    have hz : Tendsto (fun k : ℕ =>
        u (x + h) - ∑ j ∈ Finset.range k, p j (fun _ => h)) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall (fun k => norm_nonneg _)) hrem
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C)
    have hsum : Summable (fun j => p j (fun _ => h)) :=
      p.summable (hh.trans_le hrad)
    apply hsum.hasSum_iff_tendsto_nat.mpr
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => u (x + h))
      atTop (𝓝 (u (x + h)))).sub hz
