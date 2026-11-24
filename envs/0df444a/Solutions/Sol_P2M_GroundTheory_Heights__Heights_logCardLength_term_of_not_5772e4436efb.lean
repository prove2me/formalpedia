-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_logCardLength_term_of_not_5772e4436efb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:39.647794+00:00
-- url     : https://prove2.me/submissions/7a0271c0-3e78-480c-a164-96fcf3af4ebf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
noncomputable section
open GroundTheory.Heights₂.Heights.logCardLength
open Module
variable (R : Type) [CommRing R]
variable {R}
namespace GroundTheory.Heights₂.Heights.logCardLength
theorem _root_.solution (N : Type) [AddCommGroup N] [Module R N] (m : Ideal R) (hm : ¬ m.IsMaximal) :
    term R N m = 0 := by
  classical
  rw [term, finsum_eq_if, if_neg hm]
end GroundTheory.Heights₂.Heights.logCardLength
