-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliX_pauliZ_sameSite_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:43:55.6632+00:00
-- url     : https://prove2.me/submissions/c2a0ac54-bec3-4717-ad4c-d940994deb22

-- ID: af127e8c-d7bc-481c-8dfc-cd326e9dc752 | NAME: QEC.Semantics.Qubit.pauliX_pauliZ_sameSite_anticommute | 未本地编译验证
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
    pauliX * pauliZ = -(pauliZ * pauliX) := by
  ext ψ b
  fin_cases b <;>
    simp [Module.End.mul_apply, pauliX_apply, pauliZ_apply, zPhase] <;> ring
