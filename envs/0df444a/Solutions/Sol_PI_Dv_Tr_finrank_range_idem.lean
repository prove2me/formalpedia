-- Prove2me | solution 1 for PI.Dv.Tr.finrank_range_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:30.226863+00:00
-- url     : https://prove2.me/submissions/6a62262b-fa88-40ce-a4e1-d1b64147cc2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility

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
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
namespace PI.Dv.Tr
theorem _root_.solution (f : Module.End K V) (h : f * f = f) :
    ((finrank K (LinearMap.range f) : ℕ) : K) = LinearMap.trace K V f :=
  (((LinearMap.isProj_range_iff_isIdempotentElem f).mpr h).trace).symm
end PI.Dv.Tr
