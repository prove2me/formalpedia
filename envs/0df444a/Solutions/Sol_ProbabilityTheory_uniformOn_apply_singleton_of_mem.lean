-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_apply_singleton_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:44.739731+00:00
-- url     : https://prove2.me/submissions/763401d4-fd74-4b5c-a3e9-dcc86a97afbf

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution (hx : x ∈ s) (hs : s.Finite) :
    uniformOn s {x} = 1 / Nat.card s := by
  have : {x} ∩ s = {x} := by ext y; simp +contextual [hx]
  simp only [uniformOn, cond, Measure.smul_apply, MeasurableSet.singleton, Measure.restrict_apply,
    this, Measure.count_singleton', smul_eq_mul, mul_one, one_div, inv_inj]
  rw [Measure.count_apply_finite _ hs, Nat.card_eq_card_finite_toFinset hs]
end ProbabilityTheory
