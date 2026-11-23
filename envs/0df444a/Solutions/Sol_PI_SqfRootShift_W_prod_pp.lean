-- Prove2me | solution 1 for PI.SqfRootShift.W.prod_pp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:27.583688+00:00
-- url     : https://prove2.me/submissions/35176922-da1b-4ca3-982d-f26dc284d1e0

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
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
  have := Nat.prod_factorization_pow_eq_self hN
  rwa [Finsupp.prod, Nat.support_factorization] at this
end PI.SqfRootShift.W
