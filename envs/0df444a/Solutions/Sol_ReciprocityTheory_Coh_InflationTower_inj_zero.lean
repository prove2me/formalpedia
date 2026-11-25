-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.inj_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:32.499663+00:00
-- url     : https://prove2.me/submissions/139fe731-84af-4a44-b267-f28f9e6bb86a

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_H_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
noncomputable section
universe u
open Cx
open ReciprocityTheory.Coh.InflationTower
variable {R : Type u} [CommRing R]
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (L : Cx R) (π : ∀ m, Hom L (A m))
    (hT : IsTowerLim A τ L π) (x : L.H 0) (hx : ∀ m, (π m).H 0 x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : L.X 0) = 0 := by
    apply hT.ext
    intro m
    have h := hx m
    rw [H_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    exact h
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hz]
  exact Submodule.zero_mem _
end ReciprocityTheory.Coh.InflationTower
