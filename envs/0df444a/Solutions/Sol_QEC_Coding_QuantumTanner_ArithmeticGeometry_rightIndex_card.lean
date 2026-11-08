-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticGeometry.rightIndex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:42:02.829643+00:00
-- url     : https://prove2.me/submissions/d791418b-d811-4afd-92e0-182f7442c15f

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticGeometry
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constant_prime_conjugacySet


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticGeometry
open QEC.Coding.ExpanderCodes.QuaternionGenerators
universe v
variable {F K : Type v} [Field F] [Field K] [Fintype K]
namespace QEC.Coding.QuantumTanner.ArithmeticGeometry
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    Fintype.card (RightIndex f epsilon y hEpsilon hY hOne) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact card_constant_prime_conjugacySet f epsilon y hNonSquare hEpsilon hY hOne hTwo
end QEC.Coding.QuantumTanner.ArithmeticGeometry
