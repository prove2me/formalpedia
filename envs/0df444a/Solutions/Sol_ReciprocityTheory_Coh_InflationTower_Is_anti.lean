-- Prove2me | solution 1 for ReciprocityTheory.Coh.InflationTower.Is_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:59:15.475103+00:00
-- url     : https://prove2.me/submissions/34428cd0-cdf2-4e40-a5b1-01741755d5b3

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_Is_succ_subset

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
theorem _root_.solution (hc : ∀ m, (τ m).f (k+1) (c (m+1)) = c m) (m : ℕ) :
    Antitone fun j => Is A τ k c j m :=
  antitone_nat_of_succ_le fun j => Is_succ_subset A τ k c hc j m
end ReciprocityTheory.Coh.InflationTower
