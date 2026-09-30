-- Prove2me | solution 1 for RevenueManagement.rm_duopoly_littlewood_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T22:37:23.740975+00:00
-- url     : https://prove2.me/submissions/cc376457-034e-4cc9-850f-efbfd9554b20

import Mathlib
import Definitions.Def_RevenueManagement_competition

open RevenueManagement

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (D1 D2 : Ω → ℕ)
    (pL pH : ℝ) (hpH : 0 ≤ pH) (C y2 y2' : ℕ) (h : y2 ≤ y2') :
    littlewoodResponse P (spilloverDemand D1 D2 y2') pL pH C ≤
      littlewoodResponse P (spilloverDemand D1 D2 y2) pL pH C := by
  classical
  unfold littlewoodResponse
  apply Finset.sup_mono
  intro y hy
  simp only [Finset.mem_filter] at hy ⊢
  refine ⟨hy.1, hy.2.1, lt_of_lt_of_le hy.2.2 ?_⟩
  apply mul_le_mul_of_nonneg_left _ hpH
  apply ENNReal.toReal_mono (MeasureTheory.measure_ne_top P _)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_ofPred_eq, spilloverDemand] at hω ⊢
  omega
