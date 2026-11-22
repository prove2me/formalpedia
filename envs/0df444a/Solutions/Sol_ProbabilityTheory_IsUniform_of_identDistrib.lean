-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.of_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:14.284397+00:00
-- url     : https://prove2.me/submissions/3a4c1e23-bb85-460e-a5f2-bb68eebc6513

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IsUniform
theorem _root_.solution
    {Ω' : Type*} [MeasurableSpace Ω'] (h : IsUniform H X μ)
    {X' : Ω'
      → S} {μ' : Measure Ω'} (h' : IdentDistrib X X' μ μ') (hH : MeasurableSet (H : Set S)) :
    IsUniform H X' μ' := by
  constructor
  · intro x hx y hy
    rw [← h'.measure_mem_eq (MeasurableSet.singleton x),
      ← h'.measure_mem_eq (MeasurableSet.singleton y)]
    apply h.eq_of_mem hx hy
  · rw [← h'.measure_mem_eq hH.compl]
    exact h.measure_preimage_compl
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
