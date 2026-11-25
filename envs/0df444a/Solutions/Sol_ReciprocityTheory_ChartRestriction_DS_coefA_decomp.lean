-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:46.100004+00:00
-- url     : https://prove2.me/submissions/ecababb5-1d6b-4ee1-8e5f-9d2ad4ea3188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero

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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {F : Submodule ℂ X} (hFd : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, T x ∈ F) {y : X} (hy : y ∈ F) :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ F ∧ T (b i) = (θ i : ℂ) • b i := by
  haveI := hFd
  have hS : (T.restrict hF).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hF
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ F = n := ⟨_, rfl⟩
  refine ⟨n, fun i => ((inner ℂ (hS.eigenvectorBasis hn i) (⟨y, hy⟩ : F) •
      hS.eigenvectorBasis hn i : F) : X), fun i => hS.eigenvalues hn i, ?_, ?_⟩
  · have h2 := congrArg (fun z : F => (z : X)) ((hS.eigenvectorBasis hn).sum_repr' (⟨y, hy⟩ : F))
    simp only [Submodule.coe_sum] at h2
    exact h2.symm
  · intro i
    refine ⟨Submodule.coe_mem _, ?_⟩
    have hev : T ((hS.eigenvectorBasis hn i : F) : X) =
        (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : F) : X) := by
      have h3 := congrArg (fun z : F => (z : X)) (hS.apply_eigenvectorBasis hn i)
      simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
      exact h3
    beta_reduce
    rw [Submodule.coe_smul, map_smul, hev, smul_comm]
end ReciprocityTheory.ChartRestriction.DS
