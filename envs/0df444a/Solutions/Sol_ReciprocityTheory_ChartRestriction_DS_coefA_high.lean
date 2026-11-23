-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:43.104504+00:00
-- url     : https://prove2.me/submissions/3705c2aa-370b-4ba0-ab1f-84ee86ccb3d1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_inner_eq_zero

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
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : Y →ₗ[ℂ] Y} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {L : Submodule ℂ Y} (hLd : FiniteDimensional ℂ L) (hL : ∀ x ∈ L, T x ∈ L) :
    ∃ C : ℝ, ∀ F ∈ L, ∀ u : Y, ∀ θ : ℝ, C < θ → T u = (θ : ℂ) • u → inner ℂ F u = 0 := by
  haveI := hLd
  have hS : (T.restrict hL).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hL
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ L = n := ⟨_, rfl⟩
  have hev : ∀ i, T ((hS.eigenvectorBasis hn i : L) : Y) =
      (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : L) : Y) := by
    intro i
    have h3 := congrArg (fun z : L => (z : Y)) (hS.apply_eigenvectorBasis hn i)
    simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
    exact h3
  refine ⟨∑ i, |hS.eigenvalues hn i|, ?_⟩
  intro F hF u θ hθ hu
  have hle : ∀ i, hS.eigenvalues hn i ≤ ∑ j, |hS.eigenvalues hn j| := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |hS.eigenvalues hn j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have horth : ∀ i, inner ℂ ((hS.eigenvectorBasis hn i : L) : Y) u = 0 := fun i =>
    coefA_inner_eq_zero hT (hev i) hu (ne_of_lt (lt_of_le_of_lt (hle i) hθ))
  have hsum := congrArg (fun z : L => (z : Y)) ((hS.eigenvectorBasis hn).sum_repr' (⟨F, hF⟩ : L))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum, sum_inner]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_smul_left, horth i, mul_zero]
end ReciprocityTheory.ChartRestriction.DS
