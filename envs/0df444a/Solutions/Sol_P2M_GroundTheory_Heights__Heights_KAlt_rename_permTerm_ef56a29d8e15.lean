-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KAlt_rename_permTerm_ef56a29d8e15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:56.226957+00:00
-- url     : https://prove2.me/submissions/71bb3610-258e-413d-9e42-8837816d7396

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
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.KAlt
theorem _root_.solution (e : ι → ℕ) (w π : Equiv.Perm ι) :
    rename w (permTerm e π) = permTerm e (w * π) := by
  simp [permTerm, map_prod, rename_X, Equiv.Perm.mul_apply]
end GroundTheory.Heights₂.Heights.KAlt
