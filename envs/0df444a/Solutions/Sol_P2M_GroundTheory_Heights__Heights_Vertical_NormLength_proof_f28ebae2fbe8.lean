-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormLength_proof_f28ebae2fbe8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:22.850712+00:00
-- url     : https://prove2.me/submissions/bd147697-219e-41ae-b030-7e1519c67048

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ord_norm_eq_length_b38d6a2def59

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open Module
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormLength
theorem _root_.solution : NormLength.Statement := by
  intro R B _ _ _ _ _ _ _ b hb
  exact ord_norm_eq_length hb
end NormLength
end GroundTheory.Heights₂.Heights.Vertical
