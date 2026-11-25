-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.le_span_weightVecs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:37.858801+00:00
-- url     : https://prove2.me/submissions/4d0ce204-ba19-4a6f-99b7-5d341c164c89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    V ≤ Submodule.span ℂ {v | v ∈ V ∧ ∃ ν : Fin n → ℝ, ∀ a, E a a v = (ν a : ℂ) • v} := by
  haveI := hVf
  have hst : ∀ a, ∀ v ∈ V, E a a v ∈ V := fun a v hv => hVK a a rfl v hv
  let T : Fin n → Module.End ℂ V := fun a => (E a a).restrict (hst a)
  have hsym : ∀ a, (T a).IsSymmetric := by
    intro a
    refine LinearMap.IsSymmetric.restrict_invariant (T := E a a) (fun x y => ?_) (hst a)
    rw [hU a a x y]
    simp [adjSign]
  have hcomm : Pairwise (Function.onFun Commute T) := by
    intro a c _
    have h := hE a a c c
    have hEc : E a a * E c c = E c c * E a a := by
      rw [← sub_eq_zero, h]
      by_cases hac : a = c
      · subst hac
        simp
      · simp [hac, Ne.symm hac]
    show T a * T c = T c * T a
    refine LinearMap.ext fun v => Subtype.ext ?_
    show E a a (E c c v) = E c c (E a a v)
    exact congrArg (fun F : Module.End ℂ M => F (v : M)) hEc
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  intro x hx
  have hy : (⟨x, hx⟩ : V) ∈ ⨆ χ : Fin n → ℂ, ⨅ i, Module.End.eigenspace (T i) (χ i) := by
    rw [htop]
    exact Submodule.mem_top
  show ((⟨x, hx⟩ : V) : M) ∈ _
  refine Submodule.iSup_induction _ (motive := fun y : V => (y : M) ∈ Submodule.span ℂ _) hy ?_ ?_ ?_
  · intro χ y hy
    rw [Submodule.mem_iInf] at hy
    by_cases hy0 : y = 0
    · subst hy0
      exact Submodule.zero_mem _
    · have hreal : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := by
        intro a
        have hev : Module.End.HasEigenvalue (T a) (χ a) := by
          first
            | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hy a, hy0⟩
            | exact (Submodule.ne_bot_iff _).2 ⟨y, hy a, hy0⟩
        exact Complex.conj_eq_iff_re.1 ((hsym a).conj_eigenvalue_eq_self hev)
      refine Submodule.subset_span ⟨y.2, fun a => (χ a).re, fun a => ?_⟩
      have h := Module.End.mem_eigenspace_iff.1 (hy a)
      have h' := congrArg Subtype.val h
      simp only [T, LinearMap.restrict_coe_apply, Submodule.coe_smul] at h'
      rw [h', hreal a]
  · exact Submodule.zero_mem _
  · intro y z hy hz
    simpa using Submodule.add_mem _ hy hz
end ReciprocityTheory.ChartRestriction.DS
