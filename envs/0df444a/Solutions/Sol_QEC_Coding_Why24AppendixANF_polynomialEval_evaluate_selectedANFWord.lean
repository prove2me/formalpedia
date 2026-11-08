-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.polynomialEval_evaluate_selectedANFWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:43:50.219197+00:00
-- url     : https://prove2.me/submissions/4ad25515-4183-4a26-9948-75179bfb8949

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Field
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_evaluate_linearANFWord
import Theorems.Thm_QEC_Coding_Why24AppendixANF_selectedCoordinates_symm_eq_sum
import Theorems.Thm_QEC_Coding_Why24AppendixANF_polynomialEval_selectedBasisWord


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
open Why24BooleanANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (word : Word) :
    polynomialEval (fun power => evaluate word (selectedANFWord power)) =
      f1024SelectedCoordinates.symm word := by
  rw [selectedANFWord, polynomialEval_evaluate_linearANFWord]
  simp_rw [polynomialEval_selectedBasisWord]
  exact (selectedCoordinates_symm_eq_sum word).symm
end QEC.Coding.Why24AppendixANF
