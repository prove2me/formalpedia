-- Prove2me | solution 1 for ProbabilityTheory.Kernel.nonempty_of_isMarkovKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:44.876066+00:00
-- url     : https://prove2.me/submissions/8d2befc5-146f-4317-be20-72ec22f47352

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] [Nonempty α] : Nonempty β :=
  (κ <| Classical.arbitrary _).nonempty_of_neZero
end ProbabilityTheory.Kernel
