-- Prove2me | solution 1 for QEC.Semantics.Qubit.localX_square
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:45:14.880268+00:00
-- url     : https://prove2.me/submissions/43a2008d-1be7-4ad8-b7c8-131994697b53

-- ID: d74871c7-73ae-4b63-99e3-df287ebc3ba6 | NAME: QEC.Semantics.Qubit.localX_square | 未本地编译验证
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

theorem solution (i : ι) : localX i * localX i = 1 := by
  ext ψ bits
  simp [Module.End.mul_apply, localX_apply, flipAt_flipAt]
