-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:40:43.213201+00:00
-- url     : https://prove2.me/submissions/2a3ba748-53e0-49df-8f68-27d2f1cacac9

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_2_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (2 : Fin 10) < right) :
    sourcePairCoefficient 2 right = quadraticGateCoefficient 2 right := by
  fin_cases right
  · change (2 : Nat) < 0 at hlt
    omega
  · change (2 : Nat) < 1 at hlt
    omega
  · change (2 : Nat) < 2 at hlt
    omega
  · exact sourceCoefficient_pair_2_3
  · exact sourceCoefficient_pair_2_4
  · exact sourceCoefficient_pair_2_5
  · exact sourceCoefficient_pair_2_6
  · exact sourceCoefficient_pair_2_7
  · exact sourceCoefficient_pair_2_8
  · exact sourceCoefficient_pair_2_9
end QEC.Coding.Why24AppendixANF
