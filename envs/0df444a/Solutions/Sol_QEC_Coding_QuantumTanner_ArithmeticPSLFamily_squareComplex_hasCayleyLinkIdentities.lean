-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.ArithmeticPSLFamily.squareComplex_hasCayleyLinkIdentities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:42:42.817792+00:00
-- url     : https://prove2.me/submissions/57b2c020-b73c-4366-a22c-cc550c5c76c0

import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_ProjectiveLinearSize
import Definitions.Def_QEC_Coding_QuantumTanner_ArithmeticPSLFamily
import Theorems.Thm_QEC_Coding_QuantumTanner_cayleySquareComplex_hasCayleyLinkIdentities


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.ArithmeticPSLFamily
open QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
variable (p : ℕ) [hPrime : Fact p.Prime]

variable (hOdd : 3 ≤ p) (epsilon : ZMod p) (hEpsilon : epsilon ≠ 0)
namespace QEC.Coding.QuantumTanner.ArithmeticPSLFamily
theorem _root_.solution (n : ℕ) :
    (squareComplex p hOdd epsilon hEpsilon n).HasCayleyLinkIdentities :=
  cayleySquareComplex_hasCayleyLinkIdentities
    (left p hOdd epsilon hEpsilon n) (right p hOdd epsilon hEpsilon n)
    (indexedLeftInverse epsilon hEpsilon) (Equiv.refl _)
    (left_injective p hOdd epsilon hEpsilon n) (right_injective p hOdd epsilon hEpsilon n)
    (left_inverse p hOdd epsilon hEpsilon n) (right_inverse p hOdd epsilon hEpsilon n)
    (total_nonconjugacy p hOdd epsilon hEpsilon n)
end QEC.Coding.QuantumTanner.ArithmeticPSLFamily
