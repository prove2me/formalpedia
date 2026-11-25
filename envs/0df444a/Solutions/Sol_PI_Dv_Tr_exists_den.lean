-- Prove2me | solution 1 for PI.Dv.Tr.exists_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:10.12403+00:00
-- url     : https://prove2.me/submissions/4ebf9c33-a063-4825-95d0-0a50947405b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_UpperTheory_Reformulated_B_KudlaSiegelWeil_exists_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.Tr
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) {y : V} (hy : y ∈ Submodule.span K (L : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • y ∈ L :=
  _root_.UpperTheory.Reformulated.B.KudlaSiegelWeil.exists_den L hy
end PI.Dv.Tr
