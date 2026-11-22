-- Prove2me | solution 1 for P2M_ProbabilityTheory_iIndepFun_finsets_comp__3666e794ddd7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:49.295857+00:00
-- url     : https://prove2.me/submissions/4911e058-6535-4662-8ca3-0cb807d58ff6

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
universe u
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution {f : ∀ i,
  Ω → β i} {S S' : Finset ι} (h_disjoint : Disjoint S S')
    (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i, Measurable (f i))
    {γ γ' : Type u} {mγ : MeasurableSpace γ} {mγ' : MeasurableSpace γ'}
    {φ : (∀ i : S, β i) → γ} {φ' : (∀ i : S',
      β i) → γ'} (hφ : Measurable φ) (hφ' : Measurable φ') :
    IndepFun (fun a ↦ φ (fun (i : S) ↦ f i a)) (fun a ↦ φ' (fun (i : S') ↦ f i a)) μ :=
      by
  set S₂ := ![S,S']
  set γ₂ := ![γ,γ']
  set φ₂ : (j:Fin 2) → ((i: S₂ j) → β i) → γ₂ j :=
    fun j =>
      match j with
      | 0 => φ
      | 1 => φ'
  have h_disjoint₂ : Set.PairwiseDisjoint Set.univ S₂ := by
    simp_rw [Set.PairwiseDisjoint, Set.Pairwise, Fin.forall_fin_two, Function.onFun]
    simp [h_disjoint, h_disjoint.symm, S₂]
  set mγ₂ : (j:Fin 2) → MeasurableSpace (γ₂ j) := fun j ↦ match j with
  | 0 => mγ
  | 1 => mγ'
  have hφ₂ (j:Fin 2) : Measurable (φ₂ j) := match j with
  | 0 => hφ
  | 1 => hφ'
  have hneq : (0:Fin 2) ≠ (1:Fin 2) := by simp
  have hindep := (iIndepFun.finsets_comp S₂ h_disjoint₂ hf_Indep hf_meas φ₂ hφ₂).indepFun hneq
  change IndepFun (fun a ↦ φ (fun (i : S) ↦ f i a))
    (fun a ↦ φ' (fun (i : S') ↦ f i a)) μ at hindep
  exact hindep
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
