-- Prove2me | solution 1 for QEC.Coding.FinitePath.HammingWeight_single_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:26.833444+00:00
-- url     : https://prove2.me/submissions/c86d7b23-7ff7-43ab-a7d8-be3f66513027

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_FinitePath
import Theorems.Thm_QEC_Coding_FinitePath_boundary_single
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
    {Index : Type*} [Fintype Index] [DecidableEq Index] (i : Index) :
    HammingWeight (Pi.single i (1 : F) : Word F Index) ≤ 1 := by
  classical
  rw [HammingWeight_eq_card_hammingSupport]
  apply (Finset.card_le_card (s := hammingSupport
    (Pi.single i (1 : F) : Word F Index)) (t := {i}))
  intro j hj
  simp only [Finset.mem_singleton]
  by_contra hji
  have hzero : (Pi.single i (1 : F) : Word F Index) j = 0 := by
    rw [Pi.single_eq_of_ne hji]
  simp [hammingSupport, hzero] at hj
end QEC.Coding.FinitePath
