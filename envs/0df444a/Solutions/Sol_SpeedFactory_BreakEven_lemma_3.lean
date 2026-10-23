-- Prove2me | solution 1 for SpeedFactory.BreakEven.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:35:40.945314+00:00
-- url     : https://prove2.me/submissions/b9a8634f-0932-439b-8f5b-f5eb5cc8e365

import Mathlib

open MeasureTheory ProbabilityTheory Filter

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (x : ℕ → Ω → ℝ) (hind : iIndepFun x P) (hid : ∀ t, IdentDistrib (x t) (x 0) P P)
    (hL2 : MemLp (x 0) 2 P) (σx2 : ℝ) (hσx2 : variance (x 0) P = σx2)
    (g : ℕ → ℝ) (hg : Summable fun t => g t ^ 2) :
    let y : ℕ → Ω → ℝ := fun t ω => ∑ i ∈ Finset.range (t + 1), x i ω * g (t - i)
    (∀ t, variance (y t) P = σx2 * ∑ i ∈ Finset.range (t + 1), g i ^ 2) ∧
      Tendsto (fun t => variance (y t) P) atTop (nhds (σx2 * ∑' t, g t ^ 2)) := by
  intro y
  have hvar : ∀ t, variance (y t) P = σx2 * ∑ i ∈ Finset.range (t + 1), g i ^ 2 := by
    intro t
    have hy : y t = ∑ i ∈ Finset.range (t + 1), fun ω => x i ω * g (t - i) := by
      funext ω; simp [y, Finset.sum_apply]
    rw [hy, IndepFun.variance_sum]
    · simp_rw [variance_mul_const, (hid _).variance_eq, hσx2]
      rw [← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_range_reflect (fun i => g i ^ 2) (t + 1)]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      congr 2
    · intro i _
      exact ((hid i).memLp_iff.mpr hL2).mul_const _
    · intro i _ j _ hij
      exact (hind.indepFun hij).comp (measurable_id.mul_const _) (measurable_id.mul_const _)
  refine ⟨hvar, ?_⟩
  simp_rw [hvar]
  exact (hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul σx2
