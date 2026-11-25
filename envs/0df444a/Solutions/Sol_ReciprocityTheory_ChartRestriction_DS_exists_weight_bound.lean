-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.exists_weight_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:25:18.330004+00:00
-- url     : https://prove2.me/submissions/8ccbb5a9-373d-44e0-9a02-de0c63636a64

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_LayerSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound

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
theorem _root_.solution (hU : IsInfUnitary ε E) (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v ∈ V, v ≠ 0 → ∀ ν : Fin n → ℝ, (∀ a, E a a v = (ν a : ℂ) • v) →
      √(nsq (ν + rhoC ε)) ≤ R := by
  classical
  haveI := hVf
  have hT : ∀ a, {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)}.Finite := by
    intro a
    have hf : Set.Finite (Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl))) := by
      first
        | exact Module.End.finite_hasEigenvalue _
        | exact (Module.End.finite_spectrum _).subset fun μ h => h.mem_spectrum
    exact hf.preimage Complex.ofReal_injective.injOn
  have hW := Set.Finite.pi hT
  obtain ⟨B, hB⟩ := (hW.image fun ν => √(nsq (ν + rhoC ε))).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun v hv hv0 ν hν => ?_⟩
  have hmem : ν ∈ Set.pi Set.univ fun a =>
      {r : ℝ | Module.End.HasEigenvalue ((E a a).restrict (hVK a a rfl)) (r : ℂ)} := by
    intro a _
    have hx : ((E a a).restrict (hVK a a rfl)) ⟨v, hv⟩ = (ν a : ℂ) • (⟨v, hv⟩ : V) := by
      apply Subtype.ext
      simp [hν a]
    have hx0 : (⟨v, hv⟩ : V) ≠ 0 := by simpa using hv0
    first
      | exact Module.End.hasEigenvalue_of_hasEigenvector
          (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩)
      | exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hx, hx0⟩
  exact (hB ⟨ν, hmem, rfl⟩).trans (le_max_left _ _)
end ReciprocityTheory.ChartRestriction.DS
