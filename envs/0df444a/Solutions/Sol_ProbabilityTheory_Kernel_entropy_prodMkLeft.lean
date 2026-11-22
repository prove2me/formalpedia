-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_prodMkLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:39.441555+00:00
-- url     : https://prove2.me/submissions/98945bf0-2292-4ca1-929b-11fb9dcf0d29

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
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_integrable_of_finiteSupport
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7


attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
namespace ProbabilityTheory.Kernel
theorem _root_.solution [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {η : Kernel T U}
    {ν : Measure S} [IsProbabilityMeasure ν] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] [FiniteSupport ν] :
    Hk[prodMkLeft S η, ν.prod μ] = Hk[η, μ] := by
  simp_rw [entropy, prodMkLeft_apply]
  rw [integral_prod]
  swap; · exact integrable_of_finiteSupport (ν.prod μ)
  simp
end ProbabilityTheory.Kernel
