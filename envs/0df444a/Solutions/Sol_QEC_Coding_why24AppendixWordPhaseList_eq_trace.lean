-- Prove2me | solution 1 for QEC.Coding.why24AppendixWordPhaseList_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:03:34.324254+00:00
-- url     : https://prove2.me/submissions/3ffa58a4-4b70-4dfd-9b3c-dbedca184651

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
import Theorems.Thm_QEC_Coding_Why24AppendixANF_evaluate_sourcePhasePolynomial
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourcePhasePolynomial_eq_gatePhasePolynomial


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
open Why24BooleanANF
open Why24AppendixANF
namespace QEC.Coding
theorem _root_.solution
    (word : Why24AppendixANF.Word) :
    why24AppendixWordPhaseList why24AppendixGateList word =
      Algebra.trace (ZMod 2) F1024
        ((f1024SelectedCoordinates.symm word) ^ 7) := by
  rw [why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial,
    ← sourcePhasePolynomial_eq_gatePhasePolynomial,
    evaluate_sourcePhasePolynomial]
end QEC.Coding
