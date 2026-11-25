-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_thetaT_thetaT_0f229b03b9f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:22.519608+00:00
-- url     : https://prove2.me/submissions/304f0e3f-d5fa-4483-a945-bdce8a02da60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
open GroundTheory.Automorphic.ContragredientTranspose
namespace GroundTheory.Variant₂.N1.MapThetaTInvariant
theorem _root_.solution {F : Type*} [Field F] {n : ℕ} (g : GL (Fin n) F) :
    (thetaT : GL (Fin n) F ≃* GL (Fin n) F) (thetaT g) = g :=
  (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm_apply_apply g
end GroundTheory.Variant₂.N1.MapThetaTInvariant
