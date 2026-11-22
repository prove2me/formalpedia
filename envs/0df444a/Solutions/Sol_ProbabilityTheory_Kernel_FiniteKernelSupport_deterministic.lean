-- Prove2me | solution 1 for ProbabilityTheory.Kernel.FiniteKernelSupport.deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:31:24.505568+00:00
-- url     : https://prove2.me/submissions/efbc089f-8241-4313-9651-baa5a30afa49

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel.FiniteKernelSupport
theorem _root_.solution [Countable S] [Countable T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    (f : T × S → U) :
    FiniteKernelSupport (deterministic f .of_discrete) := by
  intro (t, s)
  use {f (t, s)}
  rw [Kernel.deterministic_apply' (by measurability) _ (by measurability)]
  simp
end _root_.ProbabilityTheory.Kernel.FiniteKernelSupport
end ProbabilityTheory.Kernel
