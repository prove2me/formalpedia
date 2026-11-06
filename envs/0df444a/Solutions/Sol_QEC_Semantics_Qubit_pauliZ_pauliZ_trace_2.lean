-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliZ_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:56:54.089102+00:00
-- url     : https://prove2.me/submissions/65312974-3165-4621-8bc1-ceb877b2de2c

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliZ_square
import Theorems.Thm_QEC_Semantics_Qubit_pauliI_trace

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution :
    LinearMap.trace Complex QubitSpace (pauliZ * pauliZ) = (2 : Complex) := by
  rw [pauliZ_square]
  change LinearMap.trace Complex QubitSpace pauliI = 2
  exact pauliI_trace
end QEC.Semantics.Qubit
