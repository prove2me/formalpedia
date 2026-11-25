-- Prove2me | solution 1 for PI.Dv.IdxW.finrank_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:26.850185+00:00
-- url     : https://prove2.me/submissions/1467de57-6cd8-46d8-a124-84977c766b33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan

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
variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.Dv.IdxW
theorem _root_.solution (M : Submodule R V) :
    Module.finrank K (Submodule.span K (M : Set V)) = Module.finrank R M := by
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors R) (toSpan (K := K) M) le_rfl
end PI.Dv.IdxW
