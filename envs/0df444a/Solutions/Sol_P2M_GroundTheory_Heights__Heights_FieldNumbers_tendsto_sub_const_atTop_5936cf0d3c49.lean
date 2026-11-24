-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:51.711798+00:00
-- url     : https://prove2.me/submissions/b78bb38f-9f21-4ca6-af4f-89a094764979

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (b : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.2 fun c => ⟨c + b, fun _ hm => le_sub_iff_add_le.mpr hm⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
