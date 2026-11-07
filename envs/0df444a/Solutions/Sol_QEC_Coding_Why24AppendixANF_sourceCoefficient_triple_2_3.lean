-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:11:59.509197+00:00
-- url     : https://prove2.me/submissions/a53aab7b-834b-40e4-a639-20cfa6d8287c

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part09
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_3_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (3 : Fin 10) < third) :
    sourceTripleCoefficient 2 3 third = cubicGateCoefficient 2 3 third := by
  fin_cases third
  · change (3 : Nat) < 0 at hlt
    omega
  · change (3 : Nat) < 1 at hlt
    omega
  · change (3 : Nat) < 2 at hlt
    omega
  · change (3 : Nat) < 3 at hlt
    omega
  · exact sourceCoefficient_triple_2_3_4
  · exact sourceCoefficient_triple_2_3_5
  · exact sourceCoefficient_triple_2_3_6
  · exact sourceCoefficient_triple_2_3_7
  · exact sourceCoefficient_triple_2_3_8
  · exact sourceCoefficient_triple_2_3_9
end QEC.Coding.Why24AppendixANF
