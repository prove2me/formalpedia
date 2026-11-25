-- Prove2me | solution 1 for PI.Dv.IdxW.den_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:08.943704+00:00
-- url     : https://prove2.me/submissions/98c7baa9-c4d1-43a6-ae12-8a7e054c66bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ElementDenominator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IndexCalculation_IsLocalizedModuleToSpan
import Theorems.Thm_PI_Dv_IdxW_den

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
omit [IsScalarTower R K V]
namespace PI.Dv.IdxW
theorem _root_.solution (X Y : Submodule R V) (hX : X.FG) [IsScalarTower R K V]
    (h : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y :=
  den (K := K) X Y hX fun x hx => h ▸ Submodule.subset_span hx
end PI.Dv.IdxW
