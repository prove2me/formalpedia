-- Prove2me | solution 1 for ProbabilityTheory.measurable_bandFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:06:16.299944+00:00
-- url     : https://prove2.me/submissions/57d9146c-ea95-454c-a531-be1f13e49f1d

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory

theorem solution : ∀ {A : Set Real},
  @MeasurableSet Real Real.measurableSpace A →
    ∀ (s t : Real),
      @Measurable (Prod Real Real) Real (@Prod.instMeasurableSpace Real Real Real.measurableSpace Real.measurableSpace)
        Real.measurableSpace
        (@Set.indicator (Prod Real Real) Real Real.instZero
          (@SProd.sprod (Set Real) (Set Real) (Set (Prod Real Real)) (@Set.instSProd Real Real)
            (@Set.Ioc Real Real.instPreorder s t) A)
          fun p => @Prod.snd Real Real p) := by
  intro A hA s t
  exact measurable_snd.indicator (measurableSet_Ioc.prod hA)
