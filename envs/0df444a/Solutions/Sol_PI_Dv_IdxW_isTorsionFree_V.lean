-- Prove2me | solution 1 for PI.Dv.IdxW.isTorsionFree_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:43.855383+00:00
-- url     : https://prove2.me/submissions/9af612a8-3e64-4798-b7c1-a7c2ec387941

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
variable (K)
include K
namespace PI.Dv.IdxW
theorem _root_.solution : Module.IsTorsionFree R V :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((smul_eq_zero_iff' K hr).mp h)
end PI.Dv.IdxW
