-- Prove2me | solution 1 for QEC.Semantics.Qubit.localX_localZ_sameSite_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:12:22.377223+00:00
-- url     : https://prove2.me/submissions/d8acb634-17c5-4d7d-a3ea-874d4e207347

-- ID: 4f61255c-b04a-492b-851f-66174a941d62 | NAME: QEC.Semantics.Qubit.localX_localZ_sameSite_anticommute | 未本地编译验证
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

theorem solution (i : ι) :
    localX i * localZ i = -(localZ i * localX i) := by
  ext ψ bits
  simp [Module.End.mul_apply, localX_apply, localZ_apply] <;> ring
