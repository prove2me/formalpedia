-- Prove2me | solution 1 for PI.Tr.key_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:40.520025+00:00
-- url     : https://prove2.me/submissions/044cfc16-898d-42b4-b7cf-14e83269c598

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Skeleton
import Theorems.Thm_PI_Tr_key_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution (hP : PoissonBasis) (hB : DualTransport) (hG : GaussStep) (hS : KeySmall) :
    PI.TransferenceKey := key_of (hG (hB hP)) hS
end PI.Tr
