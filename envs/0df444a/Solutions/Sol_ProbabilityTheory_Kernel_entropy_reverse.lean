-- Prove2me | solution 1 for ProbabilityTheory.Kernel.entropy_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:51.587655+00:00
-- url     : https://prove2.me/submissions/5d9dc0f1-aeb6-4508-accd-aaa501cd7197

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_map_le


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
    {κ : Kernel T (S × U × V)} [IsZeroOrMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    Hk[reverse κ, μ] = Hk[κ, μ] := by
  refine le_antisymm ?_ ?_
  · have h : reverse κ = map κ (fun p ↦ (p.2.2, p.2.1, p.1)) := reverse_eq κ
    have key := entropy_map_le (κ := κ) (μ := μ) (fun p ↦ (p.2.2, p.2.1, p.1)) hκ
    rwa [← h] at key
  · have hmap : map (reverse κ) (fun p ↦ (p.2.2, p.2.1, p.1)) = κ :=
      (reverse_eq (reverse κ)).symm.trans (reverse_reverse κ)
    have key := entropy_map_le (κ := reverse κ) (μ := μ) (fun p ↦ (p.2.2, p.2.1, p.1))
      hκ.reverse
    rwa [hmap] at key
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
