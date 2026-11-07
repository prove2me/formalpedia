-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.evaluation_mem_reedSolomonCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:13:01.465849+00:00
-- url     : https://prove2.me/submissions/9d4e0521-70fb-4c09-baa8-12b7c8a7ed8d

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l : Nat) [Fact p.Prime]
    (polynomial : Polynomial.degreeLT (ZMod p) l) :
    evaluationLinearMap p l polynomial ∈ (reedSolomonCode p l).carrier :=
  (mem_reedSolomonCode p l _).2 ⟨polynomial, rfl⟩
end QEC.Coding.KT19ReedSolomon
