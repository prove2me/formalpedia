-- Prove2me | solution 1 for P2M_GroundTheory_Variant__N1_MapThetaTInvariant_countable_valueGroupWithZero_cd8b2c53ac4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:25.279528+00:00
-- url     : https://prove2.me/submissions/f5264b6c-8d32-4779-9393-3caebcfc2521

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
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Variant₂.N1.MapThetaTInvariant
theorem _root_.solution : Countable (ValueGroupWithZero F) :=
  haveI : Countable (WithZero (Multiplicative ℤ)) := inferInstanceAs (Countable (Option ℤ))
  Countable.of_equiv _ (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toEquiv.symm
end GroundTheory.Variant₂.N1.MapThetaTInvariant
