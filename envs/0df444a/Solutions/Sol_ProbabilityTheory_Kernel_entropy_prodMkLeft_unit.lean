-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_prodMkLeft_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:50.892589+00:00
-- url     : https://prove2.me/submissions/7ab82ce7-53c5-4830-9786-cb3028736808

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
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_comap_equiv
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_prodMkLeft
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
theorem _root_.solution [MeasurableSingletonClass T]
    (κ : Kernel T S) {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] :
    Hk[prodMkLeft Unit κ, μ.map (Prod.mk ())] = Hk[κ, μ] := by
  convert entropy_comap_equiv κ (.punitProd) (μ := μ) using 2
  · ext a s _
    rw [prodMkLeft_apply, comap_apply]
    rfl
  · rw [← MeasurableEquiv.map_symm]
    congr
end ProbabilityTheory.Kernel
