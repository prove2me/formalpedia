-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul__3be578588ef6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:23.882832+00:00
-- url     : https://prove2.me/submissions/7c1ce018-7212-46a6-b008-c894187b8116

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush

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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.KAlt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (a b : Equiv.Perm ι) : sgnP (a * b) = sgnP a * sgnP b := by
  simp [sgnP, Equiv.Perm.sign_mul]
end GroundTheory.Heights₂.Heights.KAlt
