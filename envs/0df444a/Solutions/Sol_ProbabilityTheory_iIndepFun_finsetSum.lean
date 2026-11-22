-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:47.24783+00:00
-- url     : https://prove2.me/submissions/9fda1cd1-6109-4549-b8d2-01313664a324

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_iIndepFun_finsets_comp
public import Theorems.Thm_ProbabilityTheory_Kernel_iIndepFun_finsets_comp


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution
    [MeasurableSpace β'] [AddCommMonoid β'] [MeasurableAdd₂ β']
    {f : ι → Ω → β'} {J : Type*} [Finite J]
    (S : J → Finset ι) (h_disjoint : Set.PairwiseDisjoint Set.univ S)
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i)) :
    iIndepFun (fun (j : J) ↦ fun a ↦ ∑ i ∈ S j, f i a) μ := by
  set φ : (j : J) → ((i : S j) → β') → β' :=
    fun j f_j ↦ ∑ i : {i : ι // i ∈ S j}, f_j i with φ_def
  have hφ (j : J) : Measurable (φ j) := by
    rw [φ_def]
    simp only [Finset.univ_eq_attach]
    measurability
  have := iIndepFun.finsets_comp S h_disjoint hf_Indep hf_meas φ hφ
  have φ_simple (j : J) (a : Ω) : (φ j (fun i => f ↑i a)) = ∑ i ∈ S j, f i a := by
    simp only [φ_def, Finset.univ_eq_attach, ←Finset.sum_attach (S j)]
  simpa [φ_simple] using this
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
