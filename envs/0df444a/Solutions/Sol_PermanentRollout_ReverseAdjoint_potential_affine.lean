-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.potential_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/69a7edfc-7a23-48b5-b6ee-708430785058

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_FreeAffineForm_pderiv_eval
import Theorems.Thm_PermanentRollout_ReverseAdjoint_linearCombination_scaleCoefficients
import Theorems.Thm_PermanentRollout_ReverseAdjoint_linearCombination_erase_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (state : ReverseAdjoint ι)
    (values : Array (MvPolynomial ι ℂ))
    (position : ℕ) (form : FreeAffineForm ι) (input : ι)
    (hgate : values.getD position 0 = form.eval values) :
    (state.affine position form).potential values input =
      state.potential values input := by
  let family : ℕ → MvPolynomial ι ℂ :=
    fun gate => MvPolynomial.pderiv input (values.getD gate 0)
  have hderivative :
      family position =
        MvPolynomial.C (form.inputCoefficients input) +
          Finsupp.linearCombination ℂ family form.gateCoefficients := by
    dsimp [family]
    rw [hgate, FreeAffineForm.pderiv_eval]
  have herase := linearCombination_erase_add
    state.gateAdjoints family position
  change
    (state.inputAdjoints input +
      MvPolynomial.C (form.inputCoefficients input) *
        state.gateAdjoints position) +
      Finsupp.linearCombination (MvPolynomial ι ℂ) family
        (state.gateAdjoints.erase position +
          scaleCoefficients (state.gateAdjoints position)
            form.gateCoefficients) =
    state.inputAdjoints input +
      Finsupp.linearCombination (MvPolynomial ι ℂ) family
        state.gateAdjoints
  rw [map_add, linearCombination_scaleCoefficients, ← herase,
    hderivative]
  ring
end PermanentRollout.ReverseAdjoint
