-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inner_actM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:42.329582+00:00
-- url     : https://prove2.me/submissions/6ff51599-efe8-4aaf-9314-eaa3519f48fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_mem_UJset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inK_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inner_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_mem_Kset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exp_zero_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (j : V →ₗ[ℂ] H)
    (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j w = σ k (j v))
    (φ : H →L[ℂ] H) (hφ : ∀ v : V, φ ((v : D) : H) = j v)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (v : V) (x : D) :
    inner ℂ (j v) ((actM E Z x : D) : H) + inner ℂ (φ ((actM E Z v : D) : H)) (x : H) = 0 := by
  have h1 := hD.deriv Z hZ.1 (v : D)
  have h2 := hD.deriv Z hZ.1 x
  have h1' := (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h3 := HasDerivAt.inner ℂ h1' h2
  have hconst : (fun t : ℝ => inner ℂ
      (((φ.restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) ((v : D) : H)) t)
      (σ (NormedSpace.exp ((t : ℂ) • Z)) (x : H))) = fun _ => inner ℂ (j v) (x : H) := by
    funext t
    have hk := exp_mem_Kset (rorth_inK_smul hZ t)
    obtain ⟨w, hw, hwe⟩ := hVK _ hk v v.2
    have h4 := hj _ hk v ⟨w, hw⟩ hwe
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← hwe, hφ ⟨w, hw⟩, h4, rorth_inner_map hσ (rorth_mem_UJset hk)]
  rw [hconst] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', exp_zero_smul, hσ.1.1,
    one_apply_eq_self, hφ] at h5
  exact h5
end ReciprocityTheory.ChartRestriction.DS
