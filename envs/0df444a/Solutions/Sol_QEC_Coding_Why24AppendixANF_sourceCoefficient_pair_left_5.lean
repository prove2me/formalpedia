-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:43:40.317202+00:00
-- url     : https://prove2.me/submissions/c5e459dc-979c-4b62-b78d-357b7e81ff27

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_5_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_5_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_5_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_5_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (5 : Fin 10) < right) :
    sourcePairCoefficient 5 right = quadraticGateCoefficient 5 right := by
  fin_cases right
  · change (5 : Nat) < 0 at hlt
    omega
  · change (5 : Nat) < 1 at hlt
    omega
  · change (5 : Nat) < 2 at hlt
    omega
  · change (5 : Nat) < 3 at hlt
    omega
  · change (5 : Nat) < 4 at hlt
    omega
  · change (5 : Nat) < 5 at hlt
    omega
  · exact sourceCoefficient_pair_5_6
  · exact sourceCoefficient_pair_5_7
  · exact sourceCoefficient_pair_5_8
  · exact sourceCoefficient_pair_5_9
end QEC.Coding.Why24AppendixANF
