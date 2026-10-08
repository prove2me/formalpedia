-- Prove2me | solution 1 for QueueingFundamentals.GG1.one_step_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:37:54.238707+00:00
-- url     : https://prove2.me/submissions/c33f6e28-19d9-4d04-b1d4-6cd581ac6bc3

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley

open MeasureTheory in
theorem e730604c_aux (U ν : Measure ℝ) [IsFiniteMeasure U] [IsProbabilityMeasure ν]
    (hν0 : ν (Set.Iio 0) = 0) (t : ℝ) (ht : 0 ≤ t) :
    QueueingFundamentals.GG1.cdfOf (QueueingFundamentals.GG1.lindleyStep U ν) t =
      ∫ x in Set.Iic t, QueueingFundamentals.GG1.cdfOf ν (t - x) ∂U := by
  unfold QueueingFundamentals.GG1.cdfOf QueueingFundamentals.GG1.lindleyStep
  have hmeas : Measurable (fun p : ℝ × ℝ => max 0 (p.1 + p.2)) := by fun_prop
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have hpre : (fun p : ℝ × ℝ => max 0 (p.1 + p.2)) ⁻¹' Set.Iic t = {p : ℝ × ℝ | p.1 + p.2 ≤ t} := by
    ext p; simp [ht]
  have hanti : Antitone (fun x : ℝ => ν (Set.Iic (t - x))) := by
    intro a b hab; apply measure_mono; intro y hy; simp only [Set.mem_Iic] at *; linarith
  have hL : ((ν.prod U).map (fun p : ℝ × ℝ => max 0 (p.1 + p.2))) (Set.Iic t)
      = ∫⁻ x in Set.Iic t, ν (Set.Iic (t - x)) ∂U := by
    rw [Measure.map_apply hmeas measurableSet_Iic, hpre, Measure.prod_apply_symm hS]
    have hfun : (fun y : ℝ => ν ((fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ≤ t}))
        = (Set.Iic t).indicator (fun x : ℝ => ν (Set.Iic (t - x))) := by
      funext y
      have hy : (fun x : ℝ => (x, y)) ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ≤ t} = Set.Iic (t - y) := by
        ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iic]; constructor <;> intro h <;> linarith
      rw [hy]
      by_cases hyt : y ≤ t
      · rw [Set.indicator_of_mem (by simpa using hyt)]
      · rw [Set.indicator_of_notMem (by simpa using hyt)]
        refine le_antisymm ?_ (by simp)
        calc ν (Set.Iic (t - y)) ≤ ν (Set.Iio 0) := by
              apply measure_mono; intro z hz; simp only [Set.mem_Iic, Set.mem_Iio] at *; linarith
          _ = 0 := hν0
    rw [hfun, lintegral_indicator measurableSet_Iic]
  rw [measureReal_def, hL]
  simp_rw [measureReal_def]
  rw [integral_toReal hanti.measurable.aemeasurable]
  exact Filter.Eventually.of_forall (fun x => measure_lt_top _ _)

open QueueingFundamentals.GG1 MeasureTheory in
theorem solution (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsLifetimeLaw ν) (t : ℝ) (ht : 0 ≤ t) :
    cdfOf (lindleyStep (diffLaw A B) ν) t =
      ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) := by
  obtain ⟨hAp, -⟩ := hA
  obtain ⟨hBp, -⟩ := hB
  obtain ⟨hνp, hν0⟩ := hν
  have : IsFiniteMeasure (diffLaw A B) := by
    unfold diffLaw; infer_instance
  exact e730604c_aux _ ν hν0 t ht
