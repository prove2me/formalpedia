-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.puncturedReedMullerCode_dimension_eq_sum_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:14:40.070223+00:00
-- url     : https://prove2.me/submissions/94293094-c1ae-45a0-9816-f459c641b0e9

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
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
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {m r w : Nat} (hnoKernel : w < m - r) :
    Dimension (puncturedReedMullerCode r m w) =
      ∑ i ∈ Finset.Icc 0 r, Nat.choose m i := by
  simpa [binomialUpTo] using
    puncturedReedMullerCode_dimension_eq_binomialUpTo hnoKernel
end QEC.Coding.PuncturedReedMuller
