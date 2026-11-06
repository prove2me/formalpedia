-- Prove2me | solution 1 for ProbabilityTheory.measurable_levyLargeJumpSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:12:43.474272+00:00
-- url     : https://prove2.me/submissions/79ebb0fa-ea55-4d07-a806-aed00c3077e8

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory

theorem solution : ∀ {Ω : Type} [inst : MeasurableSpace Ω] {t : Real} {K : Nat → Ω → Nat} {X : Nat → Nat → Ω → Prod Real Real},
  (∀ (k : Nat), @Measurable Ω Nat inst Nat.instMeasurableSpace (K k)) →
    (∀ (k n : Nat),
        @Measurable Ω (Prod Real Real) inst
          (@Prod.instMeasurableSpace Real Real Real.measurableSpace Real.measurableSpace) (X k n)) →
      @Measurable Ω Real inst Real.measurableSpace (@ProbabilityTheory.levyLargeJumpSum Ω K X t) := by
  intro Ω inst t K X hK hX
  exact Measurable.tsum fun k =>
    ProbabilityTheory.measurable_pieceSum (hK k) (fun n => hX k n)
      (measurable_snd.indicator
        (measurableSet_Ioc.prod
          (measurableSet_le measurable_const continuous_abs.measurable)))
