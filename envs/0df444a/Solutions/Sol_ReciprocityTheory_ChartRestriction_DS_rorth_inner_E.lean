-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rorth_inner_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:12.361253+00:00
-- url     : https://prove2.me/submissions/cf31f739-b475-406d-8bad-e17206248cd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Unitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RorthFunctionalEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_actM_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_actM_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_actM_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inK_comb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rorth_inner_actM

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
    {a b : Fin n} (h : ε a = ε b) (v : V) (x : D) :
    inner ℂ (φ ((E a b v : D) : H)) (x : H) = inner ℂ (j v) ((E b a x : D) : H) := by
  have h1 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h 1) v x
  have h2 := rorth_inner_actM hσ hD hVK j hj φ hφ (rorth_inK_comb h Complex.I) v x
  simp only [rorth_actM_add, rorth_actM_smul, rorth_actM_single, LinearMap.add_apply,
    LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, star_one, map_one, map_neg,
    Complex.star_def, Complex.conj_I, neg_neg] at h1 h2
  have hI := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 -
    (1 / 2 : ℂ) * (inner ℂ (j v) ((E a b x : D) : H) + inner ℂ (j v) ((E b a x : D) : H) -
      inner ℂ (φ ((E a b v : D) : H)) (x : H) - inner ℂ (φ ((E b a v : D) : H)) (x : H)) * hI
end ReciprocityTheory.ChartRestriction.DS
