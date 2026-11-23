-- Prove2me | solution 1 for PI.SqfRootShift.W.two_le_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:52.416626+00:00
-- url     : https://prove2.me/submissions/0ff868fc-9769-43cc-bc8b-108d5dbc4eef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe
import Theorems.Thm_PI_SqfRootShift_W_le_pp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
namespace PI.SqfRootShift.W
theorem _root_.solution {N p : ℕ} (hp : p ∈ N.primeFactors) : 2 ≤ p ^ N.factorization p :=
  (Nat.prime_of_mem_primeFactors hp).two_le.trans (le_pp hp)
end PI.SqfRootShift.W
