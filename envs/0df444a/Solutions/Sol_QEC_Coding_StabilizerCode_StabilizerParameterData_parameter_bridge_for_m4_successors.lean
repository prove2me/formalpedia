-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.StabilizerParameterData.parameter_bridge_for_m4_successors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:14.772206+00:00
-- url     : https://prove2.me/submissions/4a952e5e-fe4c-4f5a-857f-547104056fde

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_encodedQubits_eq_blockLength_sub_generatorRank
import Theorems.Thm_QEC_Coding_StabilizerCode_StabilizerParameterData_semanticCodeDimension_eq_two_pow_encodedQubits

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
universe u v
open QEC.Coding.StabilizerCode
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.StabilizerParameterData
namespace QEC.Coding.StabilizerCode.StabilizerParameterData
theorem _root_.solution
    (D : StabilizerParameterData (ι := ι) (κ := κ)) :
    D.blockLength = Fintype.card ι ∧
      D.encodedQubits = D.blockLength - D.presentation.generatorRank ∧
      D.semanticCodeDimension = 2 ^ D.encodedQubits ∧
      SemanticStabilizerDistance D.presentation.code D.distance := by
  exact ⟨rfl, D.encodedQubits_eq_blockLength_sub_generatorRank,
    D.semanticCodeDimension_eq_two_pow_encodedQubits, D.semanticDistance⟩
end QEC.Coding.StabilizerCode.StabilizerParameterData
