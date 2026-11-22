-- Prove2me | solution 1 for P2M_ProbabilityTheory_Kernel_Measure_compProd_compProd__98091065f734
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:22.706647+00:00
-- url     : https://prove2.me/submissions/b57f6ff5-2fd6-4562-a33f-6c5c6f6f00f4

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_Measure_compProd_compProd

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel.Measure
theorem _root_.solution (μ : Measure T)
    (ξ : Kernel T S) (κ : Kernel (T × S) U) :
    μ ⊗ₘ (ξ ⊗ₖ κ) = (μ ⊗ₘ ξ ⊗ₘ κ).comap
      (MeasurableEquiv.prodAssoc.symm : T × S × U ≃ᵐ (T × S) × U) := by
  rw [MeasurableEquiv.comap_symm, Measure.compProd_compProd]
end _root_.ProbabilityTheory.Kernel.Measure
end ProbabilityTheory.Kernel
