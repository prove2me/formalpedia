-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:57.911692+00:00
-- url     : https://prove2.me/submissions/5bccfca2-81ae-40e7-a4ce-28b464fe7ba3

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part05
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_1_2_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (2 : Fin 10) < third) :
    sourceTripleCoefficient 1 2 third = cubicGateCoefficient 1 2 third := by
  fin_cases third
  · change (2 : Nat) < 0 at hlt
    omega
  · change (2 : Nat) < 1 at hlt
    omega
  · change (2 : Nat) < 2 at hlt
    omega
  · exact sourceCoefficient_triple_1_2_3
  · exact sourceCoefficient_triple_1_2_4
  · exact sourceCoefficient_triple_1_2_5
  · exact sourceCoefficient_triple_1_2_6
  · exact sourceCoefficient_triple_1_2_7
  · exact sourceCoefficient_triple_1_2_8
  · exact sourceCoefficient_triple_1_2_9
end QEC.Coding.Why24AppendixANF
