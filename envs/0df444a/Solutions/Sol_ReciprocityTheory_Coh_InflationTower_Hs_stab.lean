-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Hs_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:13.479228+00:00
-- url     : https://prove2.me/submissions/ad7231a3-005b-4328-82da-a3fa0c12a342

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Hs_anti

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
theorem _root_.solution (hA : ∀ m, IsArtinian R ((A m).H k)) (m : ℕ) :
    ∃ J, ∀ j, J ≤ j → Hs A τ k j m = Hs A τ k J m := by
  obtain ⟨J, hJ⟩ := IsArtinian.monotone_stabilizes
    (⟨fun j => OrderDual.toDual (Hs A τ k j m), fun _ _ h => Hs_anti A τ k m h⟩ :
      ℕ →o (Submodule R ((A m).H k))ᵒᵈ)
  exact ⟨J, fun j hj => (congrArg OrderDual.ofDual (hJ j hj)).symm⟩
end ReciprocityTheory.Coh.InflationTower
