-- Prove2me | solution 1 for PI.SqfRootsInj.W.card_nthRoots_toFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:30.6818+00:00
-- url     : https://prove2.me/submissions/1331956f-dffa-4e1b-8d16-a1a60fd47983

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_TwoPowCardPrimeFactorsLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution {K : Type*} [Field K] (N : ℕ) (a : K) :
    (nthRoots N a).toFinset.card ≤ N :=
  (Multiset.toFinset_card_le _).trans (card_nthRoots N a)
end PI.SqfRootsInj.W
