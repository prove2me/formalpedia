-- Prove2me | solution 1 for PermanentRollout.permanent_representable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/5a761ed9-29a5-4eb0-ba79-d9001b6f6824

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_arithmeticCircuit_polynomial

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution (n : ℕ) :
    ∃ circuit : ArithmeticCircuit (Fin n × Fin n),
      circuit.polynomial = permanent n := by
  exact exists_arithmeticCircuit_polynomial (permanent n)
end PermanentRollout
