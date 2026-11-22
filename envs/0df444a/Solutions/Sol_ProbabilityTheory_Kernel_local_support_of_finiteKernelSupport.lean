-- Prove2me | solution 1 for ProbabilityTheory.Kernel.local_support_of_finiteKernelSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:23.817543+00:00
-- url     : https://prove2.me/submissions/ee7468c2-48db-493a-8f30-c8f5655c6457

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
namespace _root_.ProbabilityTheory.Kernel
theorem _root_.solution
    {κ : Kernel T S} (h : FiniteKernelSupport κ) (A : Finset T) :
    ∃ B : Finset S, ∀ t ∈ A, ∀ᵐ x ∂(κ t), x ∈ B := by
  classical
  use A.biUnion (fun t ↦ (h t).choose)
  intro t ht
  change κ t (A.biUnion fun t ↦ (h t).choose)ᶜ = 0
  set B := (h t).choose
  refine measure_mono_null ?_ (h t).choose_spec
  intro s
  simp_all
end _root_.ProbabilityTheory.Kernel
end ProbabilityTheory.Kernel
