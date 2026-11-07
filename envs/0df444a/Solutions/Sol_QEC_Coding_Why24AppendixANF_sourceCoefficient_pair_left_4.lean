-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:42:10.216918+00:00
-- url     : https://prove2.me/submissions/37f02bda-8d76-437a-b4f9-4855d39549ef

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_4_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_4_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_4_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_4_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_4_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (4 : Fin 10) < right) :
    sourcePairCoefficient 4 right = quadraticGateCoefficient 4 right := by
  fin_cases right
  · change (4 : Nat) < 0 at hlt
    omega
  · change (4 : Nat) < 1 at hlt
    omega
  · change (4 : Nat) < 2 at hlt
    omega
  · change (4 : Nat) < 3 at hlt
    omega
  · change (4 : Nat) < 4 at hlt
    omega
  · exact sourceCoefficient_pair_4_5
  · exact sourceCoefficient_pair_4_6
  · exact sourceCoefficient_pair_4_7
  · exact sourceCoefficient_pair_4_8
  · exact sourceCoefficient_pair_4_9
end QEC.Coding.Why24AppendixANF
