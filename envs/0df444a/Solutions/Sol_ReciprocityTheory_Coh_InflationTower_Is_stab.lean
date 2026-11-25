-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Is_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:57.18952+00:00
-- url     : https://prove2.me/submissions/4f3fcbad-9e49-4b99-9004-a25cad55cc7f

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_torsor
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_nonempty
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_anti
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Hs_stab

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
variable (A : ℕ → Cx R) (τ : ∀ m, Hom (A (m + 1)) (A m)) (k : ℕ) (c : ∀ m, (A m).X (k + 1))
namespace ReciprocityTheory.Coh.InflationTower
theorem _root_.solution (hs : ∀ m n, Function.Surjective ((τ m).f n)) (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m)
    (hP : ∀ m, ∃ b, (A m).d k b = c m) (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Is A τ k c j m = Is A τ k c J m := by
  obtain ⟨J, hJ⟩ := Hs_stab A τ k hA m
  refine ⟨J, fun j hj => ?_⟩
  apply le_antisymm (Is_anti A τ k c hc m hj)
  obtain ⟨p, hp⟩ := Is_nonempty A τ k c hP j m
  have hpJ := Is_anti A τ k c hc m hj hp
  intro q hq
  rw [Is_torsor A τ k c hs j m p hp, hJ j hj]
  exact (Is_torsor A τ k c hs J m p hpJ q).1 hq
end ReciprocityTheory.Coh.InflationTower
