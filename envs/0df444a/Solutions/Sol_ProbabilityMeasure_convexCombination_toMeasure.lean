-- Prove2me | solution 1 for ProbabilityMeasure.convexCombination_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:42.666796+00:00
-- url     : https://prove2.me/submissions/6d2dcc08-9d5d-4741-ada3-cf82c9fde52c

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Basic

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
    (ht : t ≤ (1 : NNReal)) :
    (convexCombination μ ν t ht).toMeasure =
      t • μ.toMeasure + ((1 : NNReal) - t) • ν.toMeasure :=
  rfl
end ProbabilityMeasure
