-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.run_inputAdjoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/b43e0faa-3416-4531-addf-0b77c4db09bb

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_run_potential
import Theorems.Thm_PermanentRollout_ReverseAdjoint_run_gateAdjoints_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (circuit : FreeAffineCircuit ι)
    (output : FreeAffineForm ι) (houtput : output ∈ circuit.outputs)
    (input : ι) :
    (run circuit output).inputAdjoints input =
      MvPolynomial.pderiv input (output.eval circuit.values) := by
  have hpotential := run_potential circuit output input
  rw [potential, run_gateAdjoints_eq_zero circuit output houtput]
    at hpotential
  simpa using hpotential
end PermanentRollout.ReverseAdjoint
