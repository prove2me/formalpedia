-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_conj_one_clifford
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:09:25.114664+00:00
-- url     : https://prove2.me/submissions/2465d6e9-e59a-4828-a161-18f02d537989

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_clifford_iff
import Theorems.Thm_QEC_Coding_why24FieldClifford_one

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution :
    Why24BinaryClifford
      (why24QuditQubitUnitary.conjOperator (1 : Semantics.Operator Why24QuditSpace)) :=
  why24QuditQubitUnitary_clifford_iff _ |>.mpr why24FieldClifford_one
end QEC.Coding
