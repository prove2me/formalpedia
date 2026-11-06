-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZ_localX_commute_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:14:27.975134+00:00
-- url     : https://prove2.me/submissions/0a9e80de-df8b-4148-8811-8603a0b60a08

-- ID: d209b83b-65e2-4e93-aac7-7d981828ce8f | NAME: QEC.Semantics.Qubit.localZ_localX_commute_of_ne | 未本地编译验证
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

theorem solution {i j : ι} (h : i ≠ j) :
    localZ i * localX j = localX j * localZ i := by
  ext ψ bits
  simp [Module.End.mul_apply, localZ_apply, localX_apply, flipAt, h]
