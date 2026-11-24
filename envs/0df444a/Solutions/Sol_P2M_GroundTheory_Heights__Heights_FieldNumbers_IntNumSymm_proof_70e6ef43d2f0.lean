-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_IntNumSymm_proof_70e6ef43d2f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:44.436256+00:00
-- url     : https://prove2.me/submissions/e9d6ae6c-7eda-4bab-a8ff-b54f24602bfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mixedDiff_comp_perm_7eda8f43bc8a

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace IntNumSymm
theorem _root_.solution : IntNumSymm.Statement := by
  intro F _ K _ _ ι _ I n bs σ
  unfold intNum
  rw [mixedDiff_comp_perm]
end IntNumSymm
end GroundTheory.Heights₂.Heights.FieldNumbers
