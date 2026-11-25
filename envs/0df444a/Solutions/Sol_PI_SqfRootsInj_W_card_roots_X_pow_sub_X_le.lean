-- Prove2me | solution 1 for PI.SqfRootsInj.W.card_roots_X_pow_sub_X_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:03.592336+00:00
-- url     : https://prove2.me/submissions/c5dfbf62-eca3-4600-87f5-a0c208a288f4

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
theorem _root_.solution {K : Type*} [Field K] (M : ℕ) (hM : 2 ≤ M) :
    ((X ^ M - X : K[X]).roots.toFinset).card ≤ M := by
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp <;> omega
end PI.SqfRootsInj.W
