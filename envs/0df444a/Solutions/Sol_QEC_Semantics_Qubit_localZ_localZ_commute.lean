-- Prove2me | solution 1 for QEC.Semantics.Qubit.localZ_localZ_commute
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:12:02.026875+00:00
-- url     : https://prove2.me/submissions/4ded7fce-7159-4217-89a2-2d578d5d1460

-- ID: e8cba3af-f722-44e4-81fb-ef6077bac94a | NAME: QEC.Semantics.Qubit.localZ_localZ_commute | 未本地编译验证
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

theorem solution (i j : ι) :
    localZ i * localZ j = localZ j * localZ i := by
  ext ψ bits
  simp only [Module.End.mul_apply, localZ_apply]
  ring
