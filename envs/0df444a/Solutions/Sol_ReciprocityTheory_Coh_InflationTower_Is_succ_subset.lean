-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Is_succ_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:19.924605+00:00
-- url     : https://prove2.me/submissions/18709db7-e460-4c43-b774-b9e1a8458e18

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset

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
theorem _root_.solution (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) :
    ∀ j m, Is A τ k c (j+1) m ⊆ Is A τ k c j m := by
  intro j
  induction j with
  | zero =>
    rintro m _ ⟨b, hb, rfl⟩
    have hb' : (A (m+1)).d k b = c (m+1) := hb
    show (A m).d k ((τ m).f k b) = c m
    rw [← (τ m).comm, hb', hc]
  | succ j ih => intro m; exact Set.image_mono (ih (m+1))
end ReciprocityTheory.Coh.InflationTower
