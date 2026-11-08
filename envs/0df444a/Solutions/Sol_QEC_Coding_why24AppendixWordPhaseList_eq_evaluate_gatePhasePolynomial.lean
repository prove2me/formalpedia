-- Prove2me | solution 1 for QEC.Coding.why24AppendixWordPhaseList_eq_evaluate_gatePhasePolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:00:47.05397+00:00
-- url     : https://prove2.me/submissions/5bfece45-e2a3-4cb2-8f66-82cbcabaccd9

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Evaluation
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Certificate
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Theorems.Thm_QEC_Coding_why24AppendixGateListANF_eq_gatePhasePolynomial
import Theorems.Thm_QEC_Coding_why24AppendixWordPhaseList_eq_evaluate_gateListANF

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
      evaluate word gatePhasePolynomial := by
  rw [why24AppendixWordPhaseList_eq_evaluate_gateListANF,
    why24AppendixGateListANF_eq_gatePhasePolynomial]
end QEC.Coding
