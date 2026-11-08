-- Prove2me | solution 1 for ProbabilityTheory.HasIndependentIncrements.indepFun_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:29:23.446682+00:00
-- url     : https://prove2.me/submissions/72e1f0e3-ed50-4f15-b262-0972ebfd0fe4

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.FinCases
import Definitions.Def_LeanLevy_Processes_StochasticProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory
theorem solution {ι : Type*} {Ω : Type*} {E : Type*}
    [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]{X : ι → Ω → E} {μ : Measure Ω} (h : HasIndependentIncrements X μ)
    {s t u : ι} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ := by
  -- Define the time sequence [s, t, u] : Fin 3 → ι
  let τ : Fin 3 → ι := ![s, t, u]
  -- Show the time sequence is monotone
  have hmono : Monotone τ := Fin.monotone_iff_le_succ.mpr fun i => by
    fin_cases i
    · show s ≤ t; exact hst
    · show t ≤ u; exact htu
  -- Get iIndepFun for the two increments
  have hind := h 2 τ hmono
  -- Extract pairwise independence for indices 0 and 1
  exact hind.indepFun (i := 0) (j := 1) (by decide)
