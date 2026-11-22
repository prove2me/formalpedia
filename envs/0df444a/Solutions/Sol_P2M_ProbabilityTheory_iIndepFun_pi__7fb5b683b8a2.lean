-- Prove2me | solution 1 for P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:59.766789+00:00
-- url     : https://prove2.me/submissions/41ea716a-5338-4cd1-9f07-8203703c1f38

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_pi

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {ι Ω : Type*} {κ : ι → Type*} {α : ∀ i,
  κ i → Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [m : ∀ i j, MeasurableSpace (α i j)] {f : ∀ i j, Ω → α i j}
variable [Fintype ι] [∀ i, Fintype (κ i)]
variable {ι : Type*} {κ : ι → Type*} [∀ i, Finite (κ i)]
  {α : ∀ i, κ i → Type*} {f : ∀ i j, Ω → α i j} [m : ∀ i j, MeasurableSpace (α i j)]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution {f : ∀ ij : (Σ i, κ i), Ω → α ij.1 ij.2 }
    (f_meas : ∀ i, Measurable (f i))
    (hf : iIndepFun f μ) :
    iIndepFun (fun i ω ↦ (fun j ↦ f ⟨i, j⟩ ω)) μ :=
  iIndepFun.pi (fun _ _ ↦ f_meas _) hf
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
