-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:12:39.509042+00:00
-- url     : https://prove2.me/submissions/df0b24fa-4ec8-47cd-a923-0ec912413de6

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_5_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_5_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_5_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_3_5_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (5 : Fin 10) < third) :
    sourceTripleCoefficient 3 5 third = cubicGateCoefficient 3 5 third := by
  fin_cases third
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
  · exact sourceCoefficient_triple_3_5_6
  · exact sourceCoefficient_triple_3_5_7
  · exact sourceCoefficient_triple_3_5_8
  · exact sourceCoefficient_triple_3_5_9
end QEC.Coding.Why24AppendixANF
