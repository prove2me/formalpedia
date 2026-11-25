-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_secondCountableTopology_d896d26308ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:52.718389+00:00
-- url     : https://prove2.me/submissions/4e713c00-5a66-43bf-a2a5-01627d3cc3b9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_sigmaCompactSpace_2f9320bd201b
import Theorems.Thm_P2M_GroundTheory_Variant__N1_MapThetaTInvariant_metrizableSpace_904107939c1c

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
theorem _root_.solution : SecondCountableTopology F := by
  have := sigmaCompactSpace F
  have := metrizableSpace F
  infer_instance
end GroundTheory.Variant₂.N1.MapThetaTInvariant
