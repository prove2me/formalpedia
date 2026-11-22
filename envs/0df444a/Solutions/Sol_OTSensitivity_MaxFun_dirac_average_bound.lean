-- Prove2me | solution 1 for OTSensitivity.MaxFun.dirac_average_bound
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:25:23.215023+00:00
-- url     : https://prove2.me/submissions/c7e2b625-c8f5-4952-b89e-af0b16de868f

import Mathlib
import Theorems.Thm_OTSensitivity_MaxFun_transportCost_dirac

open MeasureTheory ProbabilityTheory OTSensitivity.MaxFun
open scoped ENNReal

theorem solution {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν ν' : Measure 𝒴) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    RWPI.SqrtLasso.transportCost k ν ν' ≤
      ∫⁻ y, RWPI.SqrtLasso.transportCost k ν (Measure.dirac y) ∂ν' := by
  simp_rw [OTSensitivity.MaxFun.transportCost_dirac k hk ν]
  have hf : (ν.prod ν').map Prod.fst = ν := by
    first | exact Measure.map_fst_prod | simp
  have hs : (ν.prod ν').map Prod.snd = ν' := by
    first | exact Measure.map_snd_prod | simp
  have hcouple : IsProbabilityMeasure (ν.prod ν') ∧
      (ν.prod ν').map Prod.fst = ν ∧ (ν.prod ν').map Prod.snd = ν' :=
    ⟨inferInstance, hf, hs⟩
  calc
    RWPI.SqrtLasso.transportCost k ν ν' ≤
        ∫⁻ w, k w.1 w.2 ∂(ν.prod ν') := by
      unfold RWPI.SqrtLasso.transportCost
      exact iInf_le_of_le (ν.prod ν') (iInf_le _ hcouple)
    _ = _ := by
      first
      | exact lintegral_prod_symm _ hk.1.measurable.aemeasurable
      | exact lintegral_prod_symm _ hk.1.measurable
      | exact?
