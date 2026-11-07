-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.polynomialEval_selectedBasisSquareWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:42:15.333458+00:00
-- url     : https://prove2.me/submissions/527affd2-574d-435e-9785-23551afe7195

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_SupportCertificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_wordMul
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisWord

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open scoped Matrix
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (selected : Fin 10) :
    polynomialEval (selectedBasisSquareWord selected) =
      f1024SelectedSelfDualBasis selected ^ 2 := by
  rw [selectedBasisSquareWord, polynomialEval_wordMul,
    polynomialEval_selectedBasisWord]
  rw [pow_two]
end QEC.Coding.Why24AppendixANF
