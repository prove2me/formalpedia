-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:12:28.278205+00:00
-- url     : https://prove2.me/submissions/2ebd6ad7-ccfd-453c-9419-80b4e2e4829c

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_4_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 3 4 third = cubicGateCoefficient 3 4 third := by
  fin_cases third
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
  · exact sourceCoefficient_triple_3_4_5
  · exact sourceCoefficient_triple_3_4_6
  · exact sourceCoefficient_triple_3_4_7
  · exact sourceCoefficient_triple_3_4_8
  · exact sourceCoefficient_triple_3_4_9
end QEC.Coding.Why24AppendixANF
