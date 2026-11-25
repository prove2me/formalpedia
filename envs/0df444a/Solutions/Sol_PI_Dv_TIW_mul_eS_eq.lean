-- Prove2me | solution 1 for PI.Dv.TIW.mul_eS_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:46:50.799606+00:00
-- url     : https://prove2.me/submissions/76f10c35-c933-4615-a475-5a6ab9d1c77a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_PI_Dv_TIW_mul_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution (z z' : MonoidAlgebra K G)
    (hz : (T.tau s).asAlgebraHom z = (T.tau s).asAlgebraHom z') : z * eS T s = z' * eS T s := by
  rw [mul_eS, mul_eS, hz]
end PI.Dv.TIW
