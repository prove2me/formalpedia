-- Prove2me | solution 1 for PI.Dv.IdxW.lenS_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:58:23.728985+00:00
-- url     : https://prove2.me/submissions/cc21eafa-546a-4638-a9a2-c09041975f4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Theorems.Thm_PI_Dv_IdxW_lenS_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.IdxW
open Module
variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {V : Type*} [AddCommGroup V] [Module R V]
namespace PI.Dv.IdxW
theorem _root_.solution (P N M : Submodule R V) (hPN : P ≤ N) (hNM : N ≤ M) :
    lenS S M N ≤ lenS S M P := by
  rw [lenS_add S P N M hPN hNM]
  exact le_self_add
end PI.Dv.IdxW
