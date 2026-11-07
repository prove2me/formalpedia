-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.boundary3_hypercubeBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:49:41.120126+00:00
-- url     : https://prove2.me/submissions/d724b636-5df7-4fbf-9e2a-d5bf354001d9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Cellulation
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PeriodicCubical4
open scoped Classical
variable {L : Nat} [NeZero L]
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution (h : Hypercube L) :
    boundary3 (hypercubeBoundary h) = 0 := by
  simp only [boundary3, hypercubeBoundary, map_add, linearize_cellWord,
    cubeBoundary]
  simp only [shift_commute]
  abel_nf
  simp
end QEC.Coding.PeriodicCubical4
