-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Hs_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:14.309207+00:00
-- url     : https://prove2.me/submissions/86020026-216c-44ac-8134-d0f7c7104ba7

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
theorem _root_.solution : ∀ j m, Hs A τ k (j+1) m ≤ Hs A τ k j m := by
  intro j
  induction j with
  | zero => intro m; exact le_top
  | succ j ih => intro m; exact Submodule.map_mono (ih (m+1))
end ReciprocityTheory.Coh.InflationTower
