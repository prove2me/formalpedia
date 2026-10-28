-- Prove2me | solution 1 for OTSensitivity.Info.theorem_8_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:53:37.571571+00:00
-- url     : https://prove2.me/submissions/14b29ba6-ba4e-4c6f-a5d1-a5b55e20b0da

import Mathlib
import Definitions.Def_OTSensitivity_Info_Setting
import Theorems.Thm_OTSensitivity_Info_relative_monotonicity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

open OTSensitivity.Info in
theorem solution {Ω 𝓧 𝓨 : Type*} [MeasurableSpace Ω] (F : MeasurableSpace 𝓧)
    [TopologicalSpace 𝓧] [PolishSpace 𝓧] [m𝓧 : MeasurableSpace 𝓧] [BorelSpace 𝓧]
    [TopologicalSpace 𝓨] [PolishSpace 𝓨] [MeasurableSpace 𝓨] [BorelSpace 𝓨]
    (k : 𝓨 → 𝓨 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝓧) (Y : Ω → 𝓨) (hX : Measurable X) (hY : Measurable Y)
    (hF : F ≤ m𝓧)
    (κ : Kernel 𝓧 𝓨) (hκ : IsCondDistrib P X Y m𝓧 κ)
    (κF : Kernel 𝓧 𝓨) (hκF : IsCondDistrib P X Y F κF) :
    OTSensitivity.MaxFun.xi k P X Y κF ≤ OTSensitivity.MaxFun.xi k P X Y κ :=
  relative_monotonicity F m𝓧 k hk P X Y hX hY hF le_rfl κF hκF κ hκ
