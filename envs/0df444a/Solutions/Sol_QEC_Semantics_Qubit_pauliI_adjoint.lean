-- Prove2me | solution 1 for QEC.Semantics.Qubit.pauliI_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:54:31.914057+00:00
-- url     : https://prove2.me/submissions/2c6c435b-d558-4973-9084-e44d548a467a

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

theorem solution : LinearMap.adjoint pauliI = pauliI := by
  solve | rfl | simp [pauliI] | simp_all [pauliI] | omega | norm_num
