-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_charFun_marginal_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:10:40.120209+00:00
-- url     : https://prove2.me/submissions/a092bb48-39ae-4278-b501-7e0e2a090537

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

private theorem chat22_increment_zero
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {X : ℝ≥0 → Ω → E} (h0 : X 0 = fun _ => 0) (t : ℝ≥0) :
    increment X 0 t = X t := by
  ext ω
  change X t ω - X 0 ω = X t ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- Source-exact Lévy marginal semigroup identity, with independence derived
directly from the independent-increments field to avoid private imports. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (s k : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + k))) ξ =
      charFun (μ.map (X s)) ξ * charFun (μ.map (X k)) ξ := by
  have hdecomp : X (s + k) = X s + increment X s (s + k) := by
    ext ω
    change X (s + k) ω = X s ω + (X (s + k) ω - X s ω)
    abel
  have hind0 : IndepFun (increment X 0 s) (increment X s (s + k)) μ := by
    let τ : Fin 3 → ℝ≥0 := ![0, s, s + k]
    have hmono : Monotone τ := Fin.monotone_iff_le_succ.mpr fun i => by
      fin_cases i
      · change (0 : ℝ≥0) ≤ s
        exact zero_le
      · exact le_self_add
    exact (h.indep_increments 2 τ hmono).indepFun (i := 0) (j := 1) (by decide)
  have hind : IndepFun (X s) (increment X s (s + k)) μ := by
    rwa [chat22_increment_zero h.start_zero] at hind0
  have hmeas_inc : Measurable (increment X s (s + k)) := by
    change Measurable (fun ω => X (s + k) ω - X s ω)
    exact (hX (s + k)).sub (hX s)
  have hconv := hind.map_add_eq_map_conv_map₀
    (hX s).aemeasurable hmeas_inc.aemeasurable
  rw [hdecomp, hconv, charFun_conv]
  have hstat := (h.stationary_increments s k).map_eq
  rw [chat22_increment_zero h.start_zero] at hstat
  rw [hstat]
