-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:46.624581+00:00
-- url     : https://prove2.me/submissions/c73e0035-489c-4078-93fe-ae03dfe7b6ec

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Theorems.Thm_ProbabilityTheory_measureEntropy_map_of_injective


set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution [MeasurableSingletonClass U]
    (κ : Kernel T S) (μ : Measure T) {f : S
      → U} (hf : Function.Injective f) (hmes : Measurable f) :
    Hk[map κ f, μ] = Hk[κ, μ] := by
  simp_rw [entropy, map_apply _ hmes, measureEntropy_map_of_injective _ _ hmes hf]
end ProbabilityTheory.Kernel
