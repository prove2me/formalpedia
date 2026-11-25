-- Prove2me | solution 1 for PI.succMin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:48.729815+00:00
-- url     : https://prove2.me/submissions/aeae5ab5-63e3-4083-833c-ecd07f0d5e37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped InnerProductSpace
open PI
variable {N : ℕ}
namespace PI
theorem _root_.solution (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : 0 ≤ succMin M i := Real.sInf_nonneg fun _ ht => ht.1
end PI
