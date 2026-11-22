-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_condKernel_compProd_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:57.855396+00:00
-- url     : https://prove2.me/submissions/eb054e2a-2815-48c2-8d57-9c9f2f5fd7ed

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_ae_eq
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_congr


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
  [Countable V] [MeasurableSingletonClass V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel
theorem _root_.solution
    [Nonempty V] (ξ : Kernel T S) [IsZeroOrMarkovKernel ξ]
    (κ : Kernel (T × S) U) [IsMarkovKernel κ] (η : Kernel (T × S × U) V) [IsMarkovKernel η]
    (μ : Measure T) :
    Hk[condKernel (ξ ⊗ₖ κ ⊗ₖ η) , μ ⊗ₘ (ξ ⊗ₖ κ)] = Hk[η,
      μ ⊗ₘ (ξ ⊗ₖ κ)] :=
  entropy_congr (condKernel_compProd_ae_eq (ξ ⊗ₖ κ) η μ)
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
