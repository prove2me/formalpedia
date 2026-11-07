-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:43:21.773035+00:00
-- url     : https://prove2.me/submissions/a6b5a452-d21f-40f0-9578-04d858bfcabb

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_7_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_7_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (7 : Fin 10) < right) :
    sourcePairCoefficient 7 right = quadraticGateCoefficient 7 right := by
  fin_cases right
  · change (7 : Nat) < 0 at hlt
    omega
  · change (7 : Nat) < 1 at hlt
    omega
  · change (7 : Nat) < 2 at hlt
    omega
  · change (7 : Nat) < 3 at hlt
    omega
  · change (7 : Nat) < 4 at hlt
    omega
  · change (7 : Nat) < 5 at hlt
    omega
  · change (7 : Nat) < 6 at hlt
    omega
  · change (7 : Nat) < 7 at hlt
    omega
  · exact sourceCoefficient_pair_7_8
  · exact sourceCoefficient_pair_7_9
end QEC.Coding.Why24AppendixANF
