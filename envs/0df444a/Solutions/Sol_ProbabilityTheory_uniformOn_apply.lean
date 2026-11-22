-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:59.241981+00:00
-- url     : https://prove2.me/submissions/b656b510-a21e-408c-af5b-0ce57e97ce8e

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
theorem _root_.solution (hs : s.Finite) (t : Set Ω) :
    uniformOn s t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  rw [uniformOn, cond_apply hs.measurableSet, count_apply_finite _ hs,
    count_apply_finite _ (hs.inter_of_left _), ← Nat.card_eq_card_finite_toFinset,
    ← Nat.card_eq_card_finite_toFinset, ENNReal.div_eq_inv_mul]
end ProbabilityTheory
