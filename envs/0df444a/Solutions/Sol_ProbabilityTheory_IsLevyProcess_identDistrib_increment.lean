-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.identDistrib_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:29:15.593364+00:00
-- url     : https://prove2.me/submissions/ccd801b8-e2d4-4a89-8575-867882f3d462

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Algebra.Group.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory
open scoped NNReal

universe u_1 u_2

theorem solution
    {Ω : Type u_1} {E : Type u_2} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [AddGroup E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (s k : ℝ≥0) :
    IdentDistrib (increment X s (s + k)) (increment X 0 k) μ μ :=
  h.stationary_increments s k
