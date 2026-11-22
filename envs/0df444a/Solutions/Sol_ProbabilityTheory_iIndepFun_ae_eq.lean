-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:51.186854+00:00
-- url     : https://prove2.me/submissions/70df6329-38d9-4b83-a1d8-00dc98461bc4

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_Finset_prod_univ_prod
public import Theorems.Thm_P2M_Finset_prod_univ_prod__3be403f26078
public import Theorems.Thm_ProbabilityTheory_EventuallyEq_finite_iInter
attribute [local simp] ProbabilityTheory.indepFun_zero_measure

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
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution {ι : Type*} {β : ι → Type*}
    {m : ∀ i, MeasurableSpace (β i)} {f g : ∀ i, Ω → β i}
    (hf_Indep : iIndepFun f μ) (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun g μ := by
  rw [iIndepFun_iff_iIndep, iIndep_iff] at hf_Indep ⊢
  intro s E H
  have (i : ι) :
      ∃ E' : Set Ω,
        i ∈ s → MeasurableSet[MeasurableSpace.comap (f i) (m i)] E' ∧ E' =ᵐ[μ] E i := by
    by_cases hi: i ∈ s
    · rcases H i hi with ⟨F, mF, hFE⟩
      use (f i)⁻¹' F
      simp only [hi, forall_const]
      constructor
      · use F
      rw [← hFE]
      exact Filter.EventuallyEq.preimage (hfg i) F
    simp_all
  classical
  rcases Classical.axiomOfChoice this with ⟨E', hE'⟩
  have hE'' : ∀ i ∈ s, MeasurableSet[MeasurableSpace.comap (f i) (m i)] (E' i) := by
    intro i hi; exact (hE' i hi).1
  have hE''' : ∀ i ∈ s, E' i =ᵐ[μ] E i := by
    intro i hi; exact (hE' i hi).2
  convert hf_Indep s hE'' using 1 with i
  · apply measure_congr
    apply EventuallyEq.finite_iInter
    intro i hi
    exact (hE''' i hi).symm
  apply Finset.prod_congr rfl
  intro i hi
  exact measure_congr (hE''' i hi).symm
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
