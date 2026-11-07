-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.restrictedNonzeroWeightSet_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:03:30.079172+00:00
-- url     : https://prove2.me/submissions/34f87bc9-92bc-403e-9fc0-a3312785d04f

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ReedMuller_evaluation_mem_reedMullerCode
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace PuncturedReedMuller
open ReedMuller
private theorem evaluation_constantPolynomial_ne_zero (m r : Nat) :
    evaluationLinearMap m r (constantPolynomial m r) ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (0 : BooleanPoint m)
  have hbasis :
      evaluationLinearMap m r (constantPolynomial m r) (0 : BooleanPoint m) = 1 := by
    rw [constantPolynomial, evaluation_basisPolynomial]
    simp [monomialValue]
  rw [hbasis] at hvalue
  exact one_ne_zero hvalue
end PuncturedReedMuller
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution (r m w : Nat) :
    (restrictedNonzeroWeightSet r m w).Nonempty := by
  let word := evaluationLinearMap m r (constantPolynomial m r)
  refine ⟨restrictedWeight w word, word, ?_, ?_, rfl⟩
  · exact evaluation_mem_reedMullerCode _
  · simpa [word] using evaluation_constantPolynomial_ne_zero m r
end QEC.Coding.PuncturedReedMuller
