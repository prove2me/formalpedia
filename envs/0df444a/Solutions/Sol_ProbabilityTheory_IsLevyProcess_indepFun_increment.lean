-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.indepFun_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:29:17.288072+00:00
-- url     : https://prove2.me/submissions/00a40049-b3db-4e83-bcd4-d26290c52622

import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_ProbabilityTheory_HasIndependentIncrements_indepFun_increment
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
    {s t u : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ :=
  h.indep_increments.indepFun_increment hst htu
