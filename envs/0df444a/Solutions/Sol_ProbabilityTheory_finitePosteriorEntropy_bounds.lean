-- Prove2me | solution 1 for ProbabilityTheory.finitePosteriorEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:16:32.403079+00:00
-- url     : https://prove2.me/submissions/74b01805-64bc-4d83-a91c-c6698385d7be

import Definitions.Def_OnlineNRM_TSFixed_OracleEntropy
import Theorems.Thm_ProbabilityTheory_condExp_simplex_ae
import Theorems.Thm_ProbabilityTheory_integral_simplex_entropy_bounds
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Data.Fintype.Card

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α] [Nonempty α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (w : Ω → α → ℝ)
    (hw : ∀ a, @Measurable Ω ℝ mΩ inferInstance (fun ω => w ω a))
    (hw0 : ∀ ω a, 0 ≤ w ω a)
    (hw1 : ∀ ω, ∑ a : α, w ω a = 1) :
    0 ≤ @finitePosteriorEntropy Ω α mΩ inferInstance P m w ∧
      @finitePosteriorEntropy Ω α mΩ inferInstance P m w ≤ Real.log (Fintype.card α : ℝ) := by
  letI : MeasurableSpace Ω := mΩ
  let q : Ω → α → ℝ := fun ω a =>
    (MeasureTheory.condExp (m₀ := mΩ) m P (fun ω' => w ω' a)) ω
  have hq := @ProbabilityTheory.condExp_simplex_ae Ω α mΩ inferInstance
    P inferInstance m hm w hw hw0 hw1
  simpa only [finitePosteriorEntropy, q] using
    (@ProbabilityTheory.integral_simplex_entropy_bounds Ω α mΩ inferInstance inferInstance
      P inferInstance q hq.1 hq.2.1 hq.2.2)
