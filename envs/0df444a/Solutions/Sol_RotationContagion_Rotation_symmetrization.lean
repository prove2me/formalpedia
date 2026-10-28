-- Prove2me | solution 1 for RotationContagion.Rotation.symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:40:06.629074+00:00
-- url     : https://prove2.me/submissions/c7ef0939-1d05-4190-b36a-a683c63e9bb3

import Definitions.Def_RotationContagion_Rotation_Model
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory RotationContagion.Rotation

private theorem schedule_integrable (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (i : Fin 2) (a b : ℝ) : IntervalIntegrable (r i) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b).mono_fun
    (hr.1 i).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa [Real.norm_eq_abs, abs_of_nonneg ((hr.2 t).1 i).1] using ((hr.2 t).1 i).2)

private theorem exposure_sum (P : Params) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (t0 : ℝ) :
    exposure P r 0 t0 + exposure P r 1 t0 = P.R := by
  unfold exposure
  rw [← intervalIntegral.integral_add (schedule_integrable r hr 0 _ _) (schedule_integrable r hr 1 _ _)]
  have he : (∫ s in t0..t0 + P.R, r 0 s + r 1 s) =
      ∫ s in t0..t0 + P.R, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact (hr.2 s).2
  rw [he]
  simp

private theorem exposure_continuous (P : Params) (r : Fin 2 → ℝ → ℝ)
    (hr : IsSchedule r) (i : Fin 2) : Continuous (exposure P r i) := by
  have hp : Continuous (fun b : ℝ => ∫ s in (0 : ℝ)..b, r i s) :=
    intervalIntegral.continuous_primitive (fun a b => schedule_integrable r hr i a b) 0
  have he : exposure P r i = fun t =>
      (∫ s in (0 : ℝ)..t + P.R, r i s) - ∫ s in (0 : ℝ)..t, r i s := by
    funext t
    have h := intervalIntegral.integral_add_adjacent_intervals
      (schedule_integrable r hr i 0 t) (schedule_integrable r hr i t (t + P.R))
    unfold exposure
    linarith only [h]
  rw [he]
  exact (hp.comp (continuous_id.add continuous_const)).sub hp

private theorem loss_continuous (P : Params) : Continuous (loss P) := by
  have he : Continuous (fun t : ℝ => Real.exp (P.γ * (t - b P))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  exact he.div (continuous_const.add he) (fun t => by positivity)

private theorem loss_bound (P : Params) (t : ℝ) : ‖loss P t‖ ≤ 1 := by
  have he : 0 < Real.exp (P.γ * (t - b P)) := Real.exp_pos _
  have hd : 0 < 1 + Real.exp (P.γ * (t - b P)) := by positivity
  rw [Real.norm_eq_abs, loss, abs_of_pos (div_pos he hd)]
  exact (div_le_one hd).mpr (by linarith)

theorem solution (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) :
    (∀ t0 : ℝ, 0 ≤ t0 → exposure P r 0 t0 + exposure P r 1 t0 = P.R) ∧
      (1 / 2 : ℝ) * ∑ ω : Fin 2, ∫ t0, loss P (exposure P r ω t0) ∂μ =
        (1 / 2 : ℝ) * ∑ ω : Fin 2,
          ∫ t0, (1 / 2 : ℝ) * (loss P (exposure P r ω t0) + loss P (P.R - exposure P r ω t0)) ∂μ := by
  have hf (i : Fin 2) : Integrable (fun t => loss P (exposure P r i t)) μ :=
    Integrable.of_bound
      ((loss_continuous P).comp (exposure_continuous P r hr i)).measurable.aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun t => loss_bound P (exposure P r i t)))
  have hswap0 (t : ℝ) : loss P (P.R - exposure P r 0 t) = loss P (exposure P r 1 t) := by
    apply congrArg (loss P)
    linarith only [exposure_sum P r hr t]
  have hswap1 (t : ℝ) : loss P (P.R - exposure P r 1 t) = loss P (exposure P r 0 t) := by
    apply congrArg (loss P)
    linarith only [exposure_sum P r hr t]
  refine ⟨fun t _ => exposure_sum P r hr t, ?_⟩
  simp only [Fin.sum_univ_two]
  simp_rw [hswap0, hswap1]
  simp only [integral_const_mul, integral_add (hf 0) (hf 1), integral_add (hf 1) (hf 0)]
  ring

#print axioms solution
