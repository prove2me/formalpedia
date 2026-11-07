-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:47.152676+00:00
-- url     : https://prove2.me/submissions/cbb462ff-3ea5-45c0-8f63-c6ecf3d607da

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_1_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (1 : Fin 10) < right) :
    sourcePairCoefficient 1 right = quadraticGateCoefficient 1 right := by
  fin_cases right
  · change (1 : Nat) < 0 at hlt
    omega
  · change (1 : Nat) < 1 at hlt
    omega
  · exact sourceCoefficient_pair_1_2
  · exact sourceCoefficient_pair_1_3
  · exact sourceCoefficient_pair_1_4
  · exact sourceCoefficient_pair_1_5
  · exact sourceCoefficient_pair_1_6
  · exact sourceCoefficient_pair_1_7
  · exact sourceCoefficient_pair_1_8
  · exact sourceCoefficient_pair_1_9
end QEC.Coding.Why24AppendixANF
