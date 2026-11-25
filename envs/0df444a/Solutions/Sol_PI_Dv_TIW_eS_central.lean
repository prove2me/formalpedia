-- Prove2me | solution 1 for PI.Dv.TIW.eS_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:49.370151+00:00
-- url     : https://prove2.me/submissions/5ad7f9cf-3ae3-4b68-bd1a-dafef74032e6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Theorems.Thm_PI_Dv_TIW_mul_eS
import Theorems.Thm_PI_Dv_TIW_eS_mul

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
theorem _root_.solution (z : MonoidAlgebra K G) : eS T s * z = z * eS T s := by
  rw [eS_mul, mul_eS]
end PI.Dv.TIW
