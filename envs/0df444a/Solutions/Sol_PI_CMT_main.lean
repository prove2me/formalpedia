-- Prove2me | solution 1 for PI.CMT.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:36.78609+00:00
-- url     : https://prove2.me/submissions/2b09a74f-3a69-487c-9099-87e567edec8a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Theorems.Thm_PI_CMT_coe_conj
import Theorems.Thm_PI_CMT_isTr_mul_fixed
import Theorems.Thm_PI_CMT_isTr_one

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
theorem _root_.solution : PI.CMTraceOnto := by
  intro L _ _ _ hL a ha
  have hfix : conj a = a := by
    apply RingOfIntegers.ext
    rw [coe_conj]
    exact ha
  obtain ⟨x, hx⟩ := isTr_mul_fixed hfix (isTr_one (K := L) hL.2.2)
  refine ⟨x, conj x, coe_conj x, ?_⟩
  rw [hx, mul_one]
end PI.CMT
