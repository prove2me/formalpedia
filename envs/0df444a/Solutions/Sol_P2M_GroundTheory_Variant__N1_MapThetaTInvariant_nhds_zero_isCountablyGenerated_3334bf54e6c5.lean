-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_nhds_zero_isCountablyGenerated_3334bf54e6c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:14.881577+00:00
-- url     : https://prove2.me/submissions/b8ca27a7-d637-406c-8bcb-c1da54262846

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_countable_valueGroupWithZero_cd8b2c53ac4b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Variant₂ GroundTheory.Variant₂.N1
open MeasureTheory Topology Filter ValuativeRel
open GroundTheory.Variant₂.N1.MapThetaTInvariant
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Variant₂.N1.MapThetaTInvariant
theorem _root_.solution : (𝓝 (0 : F)).IsCountablyGenerated := by
  have := countable_valueGroupWithZero F
  exact (IsValuativeTopology.hasBasis_nhds_zero' F).isCountablyGenerated
end GroundTheory.Variant₂.N1.MapThetaTInvariant
