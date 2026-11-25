-- Prove2me | solution 1 for PI.Dv.Tr.rankPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:46:34.962809+00:00
-- url     : https://prove2.me/submissions/88a2e55c-ee22-42ca-810f-25c6b7013cf7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_rank_identity
import Theorems.Thm_PI_Dv_Tr_rkL_cut

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
namespace PI.Dv.Tr
theorem _root_.solution : RankPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA
  have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  rw [rkT, rkL_cut A hA.1, rank_identity T P0 P hM ρ]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [rS, rkL_cut A hA.1]
end PI.Dv.Tr
