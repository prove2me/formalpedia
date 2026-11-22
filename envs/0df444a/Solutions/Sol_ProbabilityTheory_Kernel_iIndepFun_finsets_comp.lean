-- Prove2me | solution 1 for ProbabilityTheory.Kernel.iIndepFun.finsets_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:24:38.244569+00:00
-- url     : https://prove2.me/submissions/37137dc8-4fee-4500-a5fe-1110a9f08c9e

module
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace
open scoped MeasureTheory ENNReal
open ProbabilityTheory ProbabilityTheory.Kernel
variable {ι α β β' γ γ' Ω : Type*} {_mα : MeasurableSpace α} {_mΩ : MeasurableSpace Ω}
  {κ : Kernel α Ω} {μ : Measure α} {f : Ω → β} {g : Ω → β'}
variable {β γ : ι → Type*} {m : ∀ i, MeasurableSpace (β i)} {mγ : ∀ i,
  MeasurableSpace (γ i)}
  {f : ∀ i, Ω → β i}
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel.iIndepFun
theorem _root_.solution {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f κ μ) (hf_meas : ∀ i, Measurable (f i))
    (γ : J → Type*) {mγ : ∀ j, MeasurableSpace (γ j)}
    (φ : (j : J) → ((i : S j) → β i) → γ j) (hφ : ∀ j, Measurable (φ j)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ φ j (fun (i : S j) ↦ f i a)) κ μ :=
  (Kernel.iIndepFun.finsets S h_disjoint hf_Indep hf_meas).comp φ hφ
end _root_.ProbabilityTheory.Kernel.iIndepFun
end ProbabilityTheory.Kernel
