-- Prove2me | solution 1 for ProbabilityTheory.EventuallyEq.finite_iInter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:00.441146+00:00
-- url     : https://prove2.me/submissions/76e8efff-4680-4390-bfab-a8d9a7ada4fa

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic

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
variable {ι ι' : Type*} {α : ι → Type*}
    {n : (i : ι) → MeasurableSpace (α i)} {f : (i : ι) → Ω → α i}
variable {β β' Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.EventuallyEq
theorem _root_.solution
    {ι : Type*} {α : Type u_2} {l : Filter α} (s : Finset ι)
    {E : ι → Set α} {F : ι → Set α}
    (h : ∀ i ∈ s, E i =ᶠ[l] F i) :
    ⋂ i ∈ s, E i =ᶠ[l] ⋂ i ∈ s, F i :=
  Finset.eventuallyEq_iInter s h
end _root_.ProbabilityTheory.EventuallyEq
end ProbabilityTheory
