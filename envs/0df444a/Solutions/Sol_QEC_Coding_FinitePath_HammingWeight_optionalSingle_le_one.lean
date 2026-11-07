-- Prove2me | solution 1 for QEC.Coding.FinitePath.HammingWeight_optionalSingle_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:16:46.279076+00:00
-- url     : https://prove2.me/submissions/cd1440e9-1296-4b22-91e2-b23484d6e407

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_FinitePath_boundary_single
import Theorems.Thm_QEC_Coding_FinitePath_HammingWeight_single_le_one
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.FinitePath.boundary_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FinitePath
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
omit [Fintype F]
namespace QEC.Coding.FinitePath
theorem _root_.solution
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (o : Option Index) : HammingWeight (optionalSingle (F := F) o) ≤ 1 := by
  cases o with
  | none => simp [optionalSingle]
  | some i => exact HammingWeight_single_le_one (F := F) i
end QEC.Coding.FinitePath
