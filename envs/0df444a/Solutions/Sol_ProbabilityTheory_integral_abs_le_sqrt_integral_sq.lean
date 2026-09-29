-- Prove2me | solution 1 for ProbabilityTheory.integral_abs_le_sqrt_integral_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T01:23:50.666977+00:00
-- url     : https://prove2.me/submissions/035b0b8a-6e58-484f-9d6f-4e8c0398d8fa

import Theorems.Thm_ProbabilityTheory_integrable_of_integrable_sq
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) (hsq : Integrable (fun ω => (Z ω) ^ 2) μ) :
    ∫ ω, |Z ω| ∂μ ≤ Real.sqrt (∫ ω, (Z ω) ^ 2 ∂μ) := by
  have hint : Integrable Z μ := ProbabilityTheory.integrable_of_integrable_sq μ Z hZ hsq
  have habs : Integrable (fun ω => |Z ω|) μ := hint.abs
  set S : ℝ := ∫ ω, (Z ω) ^ 2 ∂μ with hS
  have hS0 : 0 ≤ S := integral_nonneg (fun ω => sq_nonneg _)
  rcases eq_or_lt_of_le hS0 with hzero | hpos
  · -- degenerate case: the square has integral zero, so `Z = 0` almost everywhere
    have hae : (fun ω => (Z ω) ^ 2) =ᵐ[μ] 0 := by
      have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (Z ω)) hsq).mp hzero.symm
      exact this
    have hae2 : (fun ω => |Z ω|) =ᵐ[μ] 0 := by
      filter_upwards [hae] with ω hω
      have : (Z ω) ^ 2 = 0 := hω
      have hz : Z ω = 0 := by nlinarith [sq_nonneg (Z ω)]
      simp [hz]
    rw [integral_congr_ae hae2]
    simp [← hzero]
  · -- main case: use `|z| ≤ ε/2 + z²/(2ε)` with `ε = √S`
    set ε : ℝ := Real.sqrt S with hε
    have hεpos : 0 < ε := Real.sqrt_pos.mpr hpos
    have hptw : ∀ ω, |Z ω| ≤ ε / 2 + (Z ω) ^ 2 / (2 * ε) := by
      intro ω
      have h := sq_nonneg (ε - |Z ω|)
      have hsqabs : |Z ω| ^ 2 = (Z ω) ^ 2 := sq_abs _
      have hkey : ε / 2 + (Z ω) ^ 2 / (2 * ε) - |Z ω| = (ε - |Z ω|) ^ 2 / (2 * ε) := by
        rw [← hsqabs]
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (ε - |Z ω|) ^ 2 / (2 * ε) :=
        div_nonneg h (by linarith)
      linarith
    have hbdint : Integrable (fun ω => ε / 2 + (Z ω) ^ 2 / (2 * ε)) μ :=
      (integrable_const _).add (hsq.div_const _)
    have hmono : ∫ ω, |Z ω| ∂μ ≤ ∫ ω, (ε / 2 + (Z ω) ^ 2 / (2 * ε)) ∂μ :=
      integral_mono habs hbdint hptw
    have hd : ∫ ω, (Z ω) ^ 2 / (2 * ε) ∂μ = S / (2 * ε) := by
      rw [integral_div]
    have hcalc : ∫ ω, (ε / 2 + (Z ω) ^ 2 / (2 * ε)) ∂μ = ε / 2 + S / (2 * ε) := by
      rw [integral_add (integrable_const _) (hsq.div_const _), hd, integral_const]
      simp
    have hfin : ε / 2 + S / (2 * ε) = ε := by
      have hsq' : ε * ε = S := Real.mul_self_sqrt hS0
      field_simp
      nlinarith [hsq']
    rw [hcalc, hfin] at hmono
    exact hmono
