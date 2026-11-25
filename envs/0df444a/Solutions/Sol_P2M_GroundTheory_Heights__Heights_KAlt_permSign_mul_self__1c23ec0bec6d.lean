-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_permSign_mul_self__1c23ec0bec6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:00:29.327956+00:00
-- url     : https://prove2.me/submissions/73422929-f6cb-4095-980b-3b9413a5f333

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
theorem _root_.solution (a : Equiv.Perm ι) : sgnP a * sgnP a = 1 := by
  unfold sgnP
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp
end GroundTheory.Heights₂.Heights.KAlt
