-- Prove2me | solution 1 for ProbabilityMeasure.convexCombination_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:45.938184+00:00
-- url     : https://prove2.me/submissions/5a0b117a-0b52-4cae-996a-bcb3cda23164

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ProbabilityMeasure
variable {Ω : Type*} [MeasurableSpace Ω]
namespace ProbabilityMeasure
theorem _root_.solution (μ ν : ProbabilityMeasure Ω) (t : NNReal)
    (ht : t ≤ (1 : NNReal))
    {s : Set Ω} (_hs : MeasurableSet s) :
    (convexCombination μ ν t ht).toMeasure s =
      (t : ENNReal) * μ.toMeasure s + (((1 : NNReal) - t : NNReal) : ENNReal) * ν.toMeasure s := by
  simp [convexCombination_toMeasure, Measure.add_apply, Measure.smul_apply]
end ProbabilityMeasure
