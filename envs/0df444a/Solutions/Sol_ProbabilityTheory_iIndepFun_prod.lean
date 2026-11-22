-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:37.7898+00:00
-- url     : https://prove2.me/submissions/25ed9c08-79d9-4249-8da9-5ad87d0aa42e

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_Finset_prod_univ_prod
public import Theorems.Thm_P2M_Finset_prod_univ_prod__3be403f26078
public import Theorems.Thm_P2M_ProbabilityTheory_iIndepFun_pi__7fb5b683b8a2
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
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution
    {hf : ∀ (i : ι), Measurable (f i)} {ST : ι' → Finset ι}
    (hS : Pairwise (Disjoint on ST)) (h : iIndepFun f μ) :
    let β := fun k ↦ Π i : ST k, α i
    iIndepFun (β := β) (fun (k : ι') (x : Ω) (i : ST k) ↦ f i x) μ := by
  let g : (i : ι') × ST i → ι := Subtype.val ∘' (Sigma.snd (α := ι'))
  have hg : Injective g := by
    intro x y hxy
    have : ¬(Disjoint on ST) x.fst y.fst := by
      refine not_forall.mpr ⟨{g y}, ?_⟩
      simp
      grind
    exact Sigma.subtype_ext (not_ne_iff.mp ((@hS x.fst y.fst).mt this)) hxy
  let m (i : ι') (j : ST i) : MeasurableSpace (α j) := n j
  exact iIndepFun.pi' (m := m) (hf ∘' g) (h.precomp hg)
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
