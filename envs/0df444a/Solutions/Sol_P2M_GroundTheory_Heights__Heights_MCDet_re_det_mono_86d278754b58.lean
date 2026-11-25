-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCDet_re_det_mono_86d278754b58
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:10.916102+00:00
-- url     : https://prove2.me/submissions/ab7dfce5-4a79-4288-bce2-de7c292d4642

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCDet_re_det_le_re_det_add_294fc9ae7455

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
namespace GroundTheory.Heights₂.Heights.MCDet
theorem _root_.solution {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    RCLike.re A.det ≤ RCLike.re B.det := by
  have := re_det_le_re_det_add hA hAB
  rwa [add_sub_cancel] at this
end GroundTheory.Heights₂.Heights.MCDet
