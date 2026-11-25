-- Prove2me | solution 1 for ReciprocityTheory.Coh.tower_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:59.096651+00:00
-- url     : https://prove2.me/submissions/6fabe364-e2d9-4835-a5af-7f74de563e72

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_IsSuccSubset
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_surj_part
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_inj_part
import Theorems.Thm_ReciprocityTheory_Coh_InflationTower_inj_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
universe u
open InflationTower
namespace ReciprocityTheory.Coh
theorem _root_.solution : TowerStatement.{u} := by
  intro R _ A τ L π hT n
  refine ⟨surj_part A τ L π hT n, fun hA x hx => ?_⟩
  cases n with
  | zero => exact inj_zero A τ L π hT x hx
  | succ k => exact inj_part A τ k L π hT (hA k rfl) x hx
end ReciprocityTheory.Coh
