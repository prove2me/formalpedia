-- Prove2me | solution 1 for PI.Dv.IdxW.isTorsionFree_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:40.054059+00:00
-- url     : https://prove2.me/submissions/79bf80db-1b83-4769-9b89-674a5a5b9eb7

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
theorem _root_.solution (M : Submodule R V) : Module.IsTorsionFree R M :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr (Subtype.ext ?_)
      have : r • (v : V) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
      exact (smul_eq_zero_iff' K hr).mp this
end PI.Dv.IdxW
