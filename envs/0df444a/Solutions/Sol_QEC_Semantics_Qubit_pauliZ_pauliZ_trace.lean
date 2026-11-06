-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliZ_pauliZ_trace
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:15:46.187202+00:00
-- url     : https://prove2.me/submissions/781caaf5-e4c9-4ea1-98cc-cd6c34d42a2c

-- ID: 4578261d-cb5d-448d-9617-4efe4f9e8a65 | NAME: QEC.Semantics.Qubit.pauliZ_pauliZ_trace | 未本地编译验证
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
    LinearMap.trace Complex QubitSpace (pauliZ * pauliZ) = (2 : Complex) := by
  have h : pauliZ * pauliZ = 1 := by
    ext ψ b
    simp only [Module.End.mul_apply, Module.End.one_apply, pauliZ_apply]
    rw [← mul_assoc, zPhase_sq, one_mul]
  rw [h]
  simp
