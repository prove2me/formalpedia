-- Prove2me | solution 1 for PermanentRollout.FreeAffineForm.pderiv_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/c3411a34-79e9-431d-9364-301ebb5a1750

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_pderiv_linearCombination
import Theorems.Thm_PermanentRollout_pderiv_input_linearCombination

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
namespace PermanentRollout
namespace FreeAffineForm
theorem _root_.solution {ι : Type*}
    (form : FreeAffineForm ι) (values : Array (MvPolynomial ι ℂ))
    (input : ι) :
    MvPolynomial.pderiv input (form.eval values) =
      MvPolynomial.C (form.inputCoefficients input) +
        Finsupp.linearCombination ℂ
          (fun gate => MvPolynomial.pderiv input
            (values.getD gate 0)) form.gateCoefficients := by
  simp only [FreeAffineForm.eval, map_add, MvPolynomial.pderiv_C,
    zero_add]
  rw [pderiv_input_linearCombination, pderiv_linearCombination]
end FreeAffineForm
end PermanentRollout
