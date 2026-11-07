-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisFourthWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:44:14.647865+00:00
-- url     : https://prove2.me/submissions/d048f292-fd16-4539-b4f6-c07e58632f95

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_wordMul
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisSquareWord

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (selected : Fin 10) :
    polynomialEval (selectedBasisFourthWord selected) =
      f1024SelectedSelfDualBasis selected ^ 4 := by
  rw [selectedBasisFourthWord, polynomialEval_wordMul,
    polynomialEval_selectedBasisSquareWord]
  ring
end QEC.Coding.Why24AppendixANF
