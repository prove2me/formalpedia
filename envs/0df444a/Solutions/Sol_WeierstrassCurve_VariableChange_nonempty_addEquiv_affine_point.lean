-- Prove2me | solution 1 for WeierstrassCurve.VariableChange.nonempty_addEquiv_affine_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8e148c8c-0b1a-5d53-bccd-31d6cb987487

import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point

set_option maxHeartbeats 3200000
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {L : Type*} [Field L] [DecidableEq L] (W : WeierstrassCurve L)
    (C : WeierstrassCurve.VariableChange L) :
    Nonempty ((C • W).toAffine.Point ≃+ W.toAffine.Point) := by

  refine ⟨(AddEquiv.mk' (variableChangeEquiv C W).symm ?_).symm⟩
  intro P Q
  exact WeierstrassCurve.Affine.Point.vcInvFun_add C W P Q

end S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point
end P2MW
export P2MW.S_WeierstrassCurve_VariableChange_nonempty_addEquiv_affine_point (solution)
