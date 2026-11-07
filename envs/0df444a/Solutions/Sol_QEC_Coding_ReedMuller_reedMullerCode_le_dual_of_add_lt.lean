-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_le_dual_of_add_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:59.476197+00:00
-- url     : https://prove2.me/submissions/40855e46-2b4e-4922-8c83-47df5c1f8d11

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ReedMuller_evaluation_pairing_eq_zero_of_add_lt
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
theorem _root_.solution {m r s : Nat}
    (hdegree : r + s < m) :
    (reedMullerCode s m).carrier ≤ (reedMullerCode r m).dual.carrier := by
  intro word hword
  rcases (mem_reedMullerCode word).1 hword with ⟨right, rfl⟩
  refine ((reedMullerCode r m).mem_dual _).2 ?_
  intro codeword hcodeword
  rcases (mem_reedMullerCode codeword).1 hcodeword with ⟨left, rfl⟩
  exact evaluation_pairing_eq_zero_of_add_lt
    (by simpa [Nat.add_comm] using hdegree) right left
end QEC.Coding.ReedMuller
