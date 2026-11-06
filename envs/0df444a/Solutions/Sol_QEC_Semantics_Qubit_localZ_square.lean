-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZ_square
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:50:18.420142+00:00
-- url     : https://prove2.me/submissions/cceacb82-576b-43e9-a2a6-86fe7e205bae

-- ID: eb9091cc-ae89-4eef-b535-ec5be8a0df0a | NAME: QEC.Semantics.Qubit.localZ_square | 未本地编译验证
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
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem solution (i : ι) : localZ i * localZ i = 1 := by
  ext ψ bits
  simp only [Module.End.mul_apply, Module.End.one_apply, localZ_apply]
  rw [← mul_assoc, zPhase_sq, one_mul]
