-- Prove2me | solution 2 for QEC.Semantics.Qubit.pauliI_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:50:33.628832+00:00
-- url     : https://prove2.me/submissions/f2ade4c1-fb09-4fb5-baec-f2bfb39e3508

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_Qubit
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators ComplexOrder
universe u
namespace QEC.Semantics.Qubit
theorem _root_.solution : LinearMap.adjoint pauliI = pauliI := by
  simp [pauliI]
end QEC.Semantics.Qubit
