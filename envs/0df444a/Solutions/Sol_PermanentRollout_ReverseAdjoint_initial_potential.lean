-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.initial_potential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/abdb0a52-5875-4288-b840-ad8196ecbacc

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_pderiv_eval
import Theorems.Thm_PermanentRollout_ReverseAdjoint_linearCombination_scaleCoefficients

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (output : FreeAffineForm ι)
    (values : Array (MvPolynomial ι ℂ)) (input : ι) :
    (initial output).potential values input =
      MvPolynomial.pderiv input (output.eval values) := by
  rw [FreeAffineForm.pderiv_eval]
  simp [potential, initial, linearCombination_scaleCoefficients]
end PermanentRollout.ReverseAdjoint
