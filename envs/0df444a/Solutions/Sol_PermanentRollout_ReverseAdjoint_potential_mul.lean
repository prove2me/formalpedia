-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.potential_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/e81599cb-932d-4fd4-a3cb-59bc347e4e74

import Mathlib
import Definitions.Def_Permanent
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
    (position left right : ℕ) (input : ι)
    (hgate : values.getD position 0 =
      values.getD left 0 * values.getD right 0) :
    (state.mul values position left right).potential values input =
      state.potential values input := by
  let family : ℕ → MvPolynomial ι ℂ :=
    fun gate => MvPolynomial.pderiv input (values.getD gate 0)
  have hderivative :
      family position =
        family left * values.getD right 0 +
          values.getD left 0 * family right := by
    dsimp [family]
    rw [hgate, MvPolynomial.pderiv_mul]
  have herase := linearCombination_erase_add
    state.gateAdjoints family position
  change
    state.inputAdjoints input +
      Finsupp.linearCombination (MvPolynomial ι ℂ) family
        (state.gateAdjoints.erase position +
          Finsupp.single left
            (state.gateAdjoints position * values.getD right 0) +
          Finsupp.single right
            (state.gateAdjoints position * values.getD left 0)) =
    state.inputAdjoints input +
      Finsupp.linearCombination (MvPolynomial ι ℂ) family
        state.gateAdjoints
  rw [map_add, map_add, Finsupp.linearCombination_single,
    Finsupp.linearCombination_single, ← herase, hderivative]
  simp only [smul_eq_mul]
  ring
end PermanentRollout.ReverseAdjoint
