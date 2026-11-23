-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_symm_eig_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:10.148844+00:00
-- url     : https://prove2.me/submissions/a5201c05-05b6-4c83-bc7d-66c52a92f371

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {T : Module.End ℂ Y} {S W : Submodule ℂ Y}
  {Q : Y →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hpos : ∀ f ∈ S, f ≠ 0 → 0 < (Q f f).re)
    (hsym : ∀ f ∈ S, ∀ g ∈ S, Q (T f) g = Q f (T g)) {u : Y} (hu : u ∈ S) (hu0 : u ≠ 0) {μ : ℂ}
    (he : T u = μ • u) : (μ.re : ℂ) = μ := by
  have h := hsym u hu u hu
  rw [he, LinearMap.map_smulₛₗ, LinearMap.smul_apply, (Q u).map_smul, smul_eq_mul, smul_eq_mul] at h
  have hq : Q u u ≠ 0 := fun h0 => by have := hpos u hu hu0; rw [h0] at this; simp at this
  have h2 : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hq h
  exact Complex.conj_eq_iff_re.mp h2
end ReciprocityTheory.ChartRestriction.DS
