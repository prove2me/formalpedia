-- Prove2me | solution 1 for PI.CMT.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:12.276688+00:00
-- url     : https://prove2.me/submissions/872e27a4-7640-4a52-96c0-76223ca8b932

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_coe_conj

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
theorem _root_.solution (x : 𝓞 K) : conj (conj x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conj, coe_conj, star_star]
end PI.CMT
