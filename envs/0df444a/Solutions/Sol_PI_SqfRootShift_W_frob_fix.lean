-- Prove2me | solution 1 for PI.SqfRootShift.W.frob_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:27.449783+00:00
-- url     : https://prove2.me/submissions/0e8f5219-c332-4797-a788-f712a179539b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
namespace PI.SqfRootShift.W
theorem _root_.solution (x : Fbar g) :
    x ^ (g ^ (minpoly (ZMod g) x).natDegree) = x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hfr := IntermediateField.adjoin.finrank hint
  have : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let _ := Fintype.ofFinite (IntermediateField.adjoin (ZMod g) {x})
  have hc : Fintype.card (IntermediateField.adjoin (ZMod g) {x}) =
      g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod g), Nat.card_zmod, hfr]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self (ZMod g) x⟩ :
      IntermediateField.adjoin (ZMod g) {x})
  rw [hc] at h
  exact congrArg Subtype.val h
end PI.SqfRootShift.W
