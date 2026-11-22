-- Prove2me | solution 1 for ProbabilityTheory.IndepFun.finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:40.182968+00:00
-- url     : https://prove2.me/submissions/824d8685-7fc2-4380-8306-7e1268925cb6

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_iIndepFun_finsetSum

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
namespace _root_.ProbabilityTheory.IndepFun
theorem _root_.solution
    [m : MeasurableSpace β'] [AddCommMonoid β'] [MeasurableAdd₂ β']
    {f : ι → Ω → β'} {s t : Finset ι} (hf_Indep : iIndepFun f μ) (hf_meas : ∀ i,
      Measurable (f i))
    (h_disj : Disjoint s t) : IndepFun (∑ i ∈ s, f i) (∑ i ∈ t, f i) μ := by
  let S : Bool → Finset ι := fun b => if b then s else t
  have h_disjoint : Set.PairwiseDisjoint Set.univ S := by
    intro b _ c _ hbc
    cases b <;> cases c
    · exact False.elim (hbc rfl)
    · change Disjoint t s
      exact h_disj.symm
    · change Disjoint s t
      exact h_disj
    · exact False.elim (hbc rfl)
  have hindep := iIndepFun.finsetSum S h_disjoint hf_Indep hf_meas
  have h_true : S true = s := by simp [S]
  have h_false : S false = t := by simp [S]
  rw [← h_true, ← h_false]
  convert hindep.indepFun Bool.true_eq_false_eq_False
  all_goals simp
end _root_.ProbabilityTheory.IndepFun
end ProbabilityTheory
