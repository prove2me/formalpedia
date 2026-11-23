-- Prove2me | solution 1 for PI.SqfRootShift.W.le_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:42:58.125021+00:00
-- url     : https://prove2.me/submissions/92d81ce3-1d6e-4e84-bb4a-4584390147d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_SumLeProdOfTwoLe

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
theorem _root_.solution {N p : ℕ} (hp : p ∈ N.primeFactors) : p ≤ p ^ N.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < N.factorization p := by
    rw [Nat.mem_primeFactors] at hp
    exact hpp.factorization_pos_of_dvd hp.2.2 hp.2.1
  exact Nat.le_self_pow hpos.ne' p
end PI.SqfRootShift.W
