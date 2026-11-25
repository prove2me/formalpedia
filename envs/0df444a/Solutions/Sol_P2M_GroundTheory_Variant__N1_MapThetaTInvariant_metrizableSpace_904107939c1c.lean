-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_metrizableSpace_904107939c1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:55.636619+00:00
-- url     : https://prove2.me/submissions/dbdd9f9d-42d5-4dca-aa06-2d14ba73a13e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_nhds_zero_isCountablyGenerated_3334bf54e6c5

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
theorem _root_.solution : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := nhds_zero_isCountablyGenerated F
  have := IsUniformAddGroup.uniformity_countably_generated (α := F)
  exact UniformSpace.metrizableSpace
end GroundTheory.Variant₂.N1.MapThetaTInvariant
