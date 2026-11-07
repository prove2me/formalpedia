-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_sum_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:56:43.359727+00:00
-- url     : https://prove2.me/submissions/a1656adf-4303-495b-92d7-59073fa3a5e6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ReedMuller_reedMullerCode_dimension_eq_binomialUpTo
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
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution (r m : Nat) :
    Dimension (reedMullerCode r m) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using reedMullerCode_dimension_eq_binomialUpTo r m
end QEC.Coding.ReedMuller
