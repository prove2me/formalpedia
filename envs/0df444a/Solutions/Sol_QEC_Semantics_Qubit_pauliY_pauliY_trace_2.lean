-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliY_pauliY_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:53:05.413226+00:00
-- url     : https://prove2.me/submissions/21642265-015e-4f0d-880c-9c0d30988180

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_Qubit_pauliY_square
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
    LinearMap.trace Complex QubitSpace (pauliY * pauliY) = (2 : Complex) := by
  rw [pauliY_square]
  change LinearMap.trace Complex QubitSpace pauliI = 2
  exact pauliI_trace
end QEC.Semantics.Qubit
