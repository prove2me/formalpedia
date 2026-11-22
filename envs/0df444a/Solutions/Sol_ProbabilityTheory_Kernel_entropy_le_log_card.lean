-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:25.39324+00:00
-- url     : https://prove2.me/submissions/7833a3dc-2038-4b0d-90e6-b5909d5cb9ed

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_measureEntropy_le_log_card
public import Theorems.Thm_ProbabilityTheory_measureEntropy_nonneg
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7


attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_const

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution
   [MeasurableSingletonClass S]
   (κ : Kernel T S) (μ : Measure T) [Fintype S] [IsProbabilityMeasure μ] :
    Hk[κ, μ] ≤ log (Fintype.card S) := by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp
end ProbabilityTheory.Kernel
