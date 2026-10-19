-- Prove2me | solution 1 for PermanentRollout.circuitComplexity_le_of_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/108f55a8-0b18-489d-8a46-3722138f3318

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {ι : Type}
    {polynomial : MvPolynomial ι ℂ} (circuit : ArithmeticCircuit ι)
    (hpolynomial : circuit.polynomial = polynomial) :
    circuitComplexity polynomial ≤ circuit.size := by
  exact Nat.sInf_le ⟨circuit, hpolynomial, rfl⟩
end PermanentRollout
