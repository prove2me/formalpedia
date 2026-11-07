-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:41:48.148833+00:00
-- url     : https://prove2.me/submissions/5e706f8b-da94-4944-92d1-82033839be04

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_3_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (3 : Fin 10) < right) :
    sourcePairCoefficient 3 right = quadraticGateCoefficient 3 right := by
  fin_cases right
  · change (3 : Nat) < 0 at hlt
    omega
  · change (3 : Nat) < 1 at hlt
    omega
  · change (3 : Nat) < 2 at hlt
    omega
  · change (3 : Nat) < 3 at hlt
    omega
  · exact sourceCoefficient_pair_3_4
  · exact sourceCoefficient_pair_3_5
  · exact sourceCoefficient_pair_3_6
  · exact sourceCoefficient_pair_3_7
  · exact sourceCoefficient_pair_3_8
  · exact sourceCoefficient_pair_3_9
end QEC.Coding.Why24AppendixANF
