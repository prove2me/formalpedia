-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliI_square
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:46:58.568203+00:00
-- url     : https://prove2.me/submissions/5577ab29-4b20-4b40-9c2b-089316c6015a

-- ID: 3780e4ae-8053-40d4-b71e-36ee05709d35 | NAME: QEC.Semantics.Qubit.pauliI_square | 未本地编译验证
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

theorem solution : pauliI * pauliI = pauliI := by
  simp [pauliI]
