-- Prove2me | solution 1 for RotationContagion.Rotation.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:00:19.804928+00:00
-- url     : https://prove2.me/submissions/42462d51-b697-4d36-94c6-59c6964603c5

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

open MeasureTheory Set Filter

namespace RotContL2

open RotationContagion.Rotation

lemma ii_of_bdd (g : ℝ → ℝ) (hg : Measurable g) (hb : ∀ s, g s ∈ Icc (0:ℝ) 1) (a c : ℝ) :
    IntervalIntegrable g volume a c := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_ hg.aestronglyMeasurable ?_
  · exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  · exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb s).1, (hb s).2]

lemma loss_bdd (P : Params) (x : ℝ) : |loss P x| ≤ 1 := by
  unfold loss
  have h := Real.exp_pos (P.γ * (x - b P))
  rw [abs_le]
  constructor
  · have : 0 ≤ Real.exp (P.γ * (x - b P)) / (1 + Real.exp (P.γ * (x - b P))) := by positivity
    linarith
  · rw [div_le_one (by linarith)]; linarith

lemma exp_sum (P : Params) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (t0 : ℝ) :
    exposure P r 0 t0 + exposure P r 1 t0 = P.R := by
  unfold exposure
  rw [← intervalIntegral.integral_add (ii_of_bdd _ (hr.1 0) (fun s => (hr.2 s).1 0) _ _)
    (ii_of_bdd _ (hr.1 1) (fun s => (hr.2 s).1 1) _ _)]
  have : ∀ s, r 0 s + r 1 s = 1 := fun s => (hr.2 s).2
  simp only [this, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

lemma exp_mem (P : Params) (hP : P.Standing) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (ω : Fin 2) (t0 : ℝ) : exposure P r ω t0 ∈ Icc 0 P.R := by
  have hR := hP.2.2
  have hle : t0 ≤ t0 + P.R := by linarith
  have hii := ii_of_bdd _ (hr.1 ω) (fun s => (hr.2 s).1 ω)
  unfold exposure
  constructor
  · exact intervalIntegral.integral_nonneg hle (fun s _ => ((hr.2 s).1 ω).1)
  · have := intervalIntegral.integral_mono_on hle (hii _ _) intervalIntegrable_const
      (fun s _ => ((hr.2 s).1 ω).2)
    simpa using this

lemma exp_cont (P : Params) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) (ω : Fin 2) :
    Continuous (fun t0 => exposure P r ω t0) := by
  have hii := ii_of_bdd _ (hr.1 ω) (fun s => (hr.2 s).1 ω)
  have hF := intervalIntegral.continuous_primitive hii 0
  have : (fun t0 => exposure P r ω t0) =
      fun t0 => (∫ s in (0:ℝ)..t0 + P.R, r ω s) - ∫ s in (0:ℝ)..t0, r ω s := by
    funext t0
    unfold exposure
    rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
  rw [this]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

end RotContL2

open RotationContagion.Rotation RotContL2 in
theorem solution (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) :
    (1 / 2 : ℝ) * ∑ ω : Fin 2, ∫ t0, exposure P r ω t0 ∂μ = P.R / 2 ∧
      ∀ T : ℝ,
        (1 / 2 : ℝ) * ∑ ω : Fin 2, μ.real {t0 | exposure P r ω t0 ≤ T} =
          (1 / 2 : ℝ) * ∑ ω : Fin 2, μ.real {t0 | P.R - T ≤ exposure P r ω t0} := by
  have hint : ∀ ω, Integrable (fun t0 => exposure P r ω t0) μ := fun ω =>
    Integrable.of_bound (exp_cont P r hr ω).aestronglyMeasurable P.R
      (Eventually.of_forall fun t0 => by
        have := exp_mem P hP r hr ω t0
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  constructor
  · rw [Fin.sum_univ_two, ← integral_add (hint 0) (hint 1)]
    simp only [exp_sum P r hr, integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  · intro T
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have e1 : {t0 | exposure P r 1 t0 ≤ T} = {t0 | P.R - T ≤ exposure P r 0 t0} := by
      ext t0; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith [exp_sum P r hr t0]
    have e0 : {t0 | exposure P r 0 t0 ≤ T} = {t0 | P.R - T ≤ exposure P r 1 t0} := by
      ext t0; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith [exp_sum P r hr t0]
    rw [e0, e1]; ring
