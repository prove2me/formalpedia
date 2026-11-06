-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.StabilizerParameterData.semanticCodeDimension_eq_two_pow_encodedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:10:44.224949+00:00
-- url     : https://prove2.me/submissions/eb7d4f37-7521-403d-91e7-6a882450fa90

import Definitions.Def_QEC_Coding_Stabilizer_Distance
import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_semanticCode_finrank_eq_two_pow_encodedQubits

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
    D.semanticCodeDimension = 2 ^ D.encodedQubits :=
  D.presentation.semanticCode_finrank_eq_two_pow_encodedQubits
end QEC.Coding.StabilizerCode.StabilizerParameterData
