-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.StabilizerParameterData.encodedQubits_eq_blockLength_sub_generatorRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:49:22.809147+00:00
-- url     : https://prove2.me/submissions/fd72a940-34fb-44de-9fc2-36c7f26daa21

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_encodedQubits_eq_blockLength_sub_generatorRank

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
    D.encodedQubits = D.blockLength - D.presentation.generatorRank :=
  D.presentation.encodedQubits_eq_blockLength_sub_generatorRank
end QEC.Coding.StabilizerCode.StabilizerParameterData
