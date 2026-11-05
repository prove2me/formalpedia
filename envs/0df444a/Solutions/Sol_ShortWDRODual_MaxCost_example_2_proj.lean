-- Prove2me | solution 1 for ShortWDRODual.MaxCost.example_2_proj
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:14:14.457219+00:00
-- url     : https://prove2.me/submissions/983541ca-3c7d-486f-b729-39b9f954bec7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Theorems.Thm_BertsekasShreve_AnalyticSelection_analytic_universallyMeasurable

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat] :
    ShortWDRODual.IP.Proj Phat := by
  -- a Polish space is a Borel space in the sense of Bertsekas–Shreve (Definition 7.7)
  have hB : BertsekasShreve.AnalyticSelection.IsBorelSpace X := by
    letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
    exact ⟨⟨X, inferInstance, inferInstance, inferInstance, Set.univ, MeasurableSet.univ,
      ⟨(Homeomorph.Set.univ X).symm⟩⟩⟩
  intro A hA
  have hAn : AnalyticSet A := hA.1.analyticSet
  have hpr : AnalyticSet (Prod.fst '' A) := hAn.image_of_continuous continuous_fst
  exact BertsekasShreve.AnalyticSelection.analytic_universallyMeasurable _ hpr Phat inferInstance
