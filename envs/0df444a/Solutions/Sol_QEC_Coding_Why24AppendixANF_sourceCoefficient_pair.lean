-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:03.569193+00:00
-- url     : https://prove2.me/submissions/1e55041f-d801-4944-8ed6-744a475caad6

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Certificate
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_0
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_1
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_left_8


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (left right : Fin 10) (hlt : left < right) :
    sourcePairCoefficient left right = quadraticGateCoefficient left right := by
  fin_cases left
  · exact sourceCoefficient_pair_left_0 right hlt
  · exact sourceCoefficient_pair_left_1 right hlt
  · exact sourceCoefficient_pair_left_2 right hlt
  · exact sourceCoefficient_pair_left_3 right hlt
  · exact sourceCoefficient_pair_left_4 right hlt
  · exact sourceCoefficient_pair_left_5 right hlt
  · exact sourceCoefficient_pair_left_6 right hlt
  · exact sourceCoefficient_pair_left_7 right hlt
  · exact sourceCoefficient_pair_left_8 right hlt
  · change (9 : Nat) < right.val at hlt
    omega
end QEC.Coding.Why24AppendixANF
