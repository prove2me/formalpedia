-- Prove2me | solution 1 for PI.Dv.ProjAW.rk_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:50.792907+00:00
-- url     : https://prove2.me/submissions/90d6a19d-bff5-47e0-b0c4-75493f5e0ea0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Theorems.Thm_PI_Dv_ProjAW_span_imgE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (hG : A.Good) (f : Module.End K A.V) : Formalism.HN.rkK (imgE A f A.L) = dimE A f := by
  unfold Formalism.HN.rkK dimE
  rw [span_imgE A hG f]
end PI.Dv.ProjAW
