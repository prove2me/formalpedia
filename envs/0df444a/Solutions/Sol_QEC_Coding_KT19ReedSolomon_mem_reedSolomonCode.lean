-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:10:35.029323+00:00
-- url     : https://prove2.me/submissions/e19c6e13-1443-4232-a935-1c83e66b1f22

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
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
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution (p l : Nat) [Fact p.Prime]
    (word : Word (ZMod p) (ZMod p)) :
    word ∈ (reedSolomonCode p l).carrier ↔
      ∃ polynomial : Polynomial.degreeLT (ZMod p) l,
        evaluationLinearMap p l polynomial = word := by
  simp [reedSolomonCode]
end QEC.Coding.KT19ReedSolomon
