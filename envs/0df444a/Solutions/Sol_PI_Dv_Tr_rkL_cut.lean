-- Prove2me | solution 1 for PI.Dv.Tr.rkL_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:02.538732+00:00
-- url     : https://prove2.me/submissions/9b1284c5-d0cb-4af1-ab43-800f0c16fc73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_span_cut

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
variable [StarRing K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (ρ : Representation K G A.V) (a : MonoidAlgebra K G) :
    rkL A (cut A ρ a A.L) = finrank K (LinearMap.range (ρ.asAlgebraHom a)) := by
  unfold rkL Formalism.HN.rkK cut cutE
  rw [span_cut A.L hA.2.2]
end PI.Dv.Tr
