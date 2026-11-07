-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.index_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:21:05.497475+00:00
-- url     : https://prove2.me/submissions/a0e6fe95-08c3-4fe9-8ce2-eead314aa87c

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndex_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable (p : ℕ) [hPrime : Fact p.Prime]

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
include hOdd
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
theorem _root_.solution (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    Fintype.card (TorusIndex epsilon) = p + 1 := by
  rw [torusIndex_card epsilon hNonSquare (two_ne_zero p hOdd), ZMod.card]
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
