-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_pauliX_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:12:23.616148+00:00
-- url     : https://prove2.me/submissions/309d4a63-0078-4b69-9117-67d0c3574265

-- ID: d02226b4-5f1b-41cf-8679-9c2d9e85cdad | NAME: QEC.Semantics.Qubit.pauliX_pauliX_trace | 未本地编译验证
import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u

theorem solution :
    LinearMap.trace Complex QubitSpace (pauliX * pauliX) = (2 : Complex) := by
  have hXX : pauliX * pauliX = 1 := by
    ext ψ b
    simp [Module.End.mul_apply, Module.End.one_apply, pauliX_apply, flipBit_flip]
  rw [hXX]
  simp [QubitSpace]
