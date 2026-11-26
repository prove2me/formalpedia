-- Prove2me | solution 1 for TunnellMap.targetLiftSign_eq_aResidualSign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:29:43.312687+00:00
-- url     : https://prove2.me/submissions/0e316e82-99ca-49d2-ab15-942d66b8bbed

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
import Theorems.Thm_TunnellMap_FreeInvolution_signAct_inj_sign
import Theorems.Thm_TunnellMap_aResidualSign_mem
import Theorems.Thm_TunnellMap_aResidual_decomposition
import Theorems.Thm_TunnellMap_residualTarget_decomposition
import Theorems.Thm_TunnellMap_targetLiftSign_mem


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hnpos : 0 < n)
    (y : AResidual n) :
    targetLiftSign (residualTargetLift y) = aResidualSign hnpos y := by
  refine (aResidualInvolution n hnpos).signAct_inj_sign
    (x := canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit y))
    (targetLiftSign_mem _) (aResidualSign_mem hnpos y) ?_
  show signActA hnpos (targetLiftSign (residualTargetLift y))
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit y)) =
    signActA hnpos (aResidualSign hnpos y)
      (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit y))
  rw [residualTarget_decomposition hnpos y, aResidual_decomposition hnpos y]
end TunnellMap
