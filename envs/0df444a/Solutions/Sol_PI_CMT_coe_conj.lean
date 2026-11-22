-- Prove2me | solution 1 for PI.CMT.coe_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:00.942795+00:00
-- url     : https://prove2.me/submissions/fa6fc804-b7d2-4a30-bac8-7f3bf0bf110f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CMT
open NumberField
variable {K : Type*} [Field K] [StarRing K]
namespace PI.CMT
theorem _root_.solution (x : 𝓞 K) : ((conj x : 𝓞 K) : K) = star (x : K) := rfl
end PI.CMT
