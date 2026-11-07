-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_2_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:33:47.114211+00:00
-- url     : https://prove2.me/submissions/03b9eb71-ad95-42ba-bcc7-1a5ca9ea9b0c

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part11
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_6_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_6_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_2_6_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 2 6 third = cubicGateCoefficient 2 6 third := by
  fin_cases third
  · change (6 : Nat) < 0 at hlt
    omega
  · change (6 : Nat) < 1 at hlt
    omega
  · change (6 : Nat) < 2 at hlt
    omega
  · change (6 : Nat) < 3 at hlt
    omega
  · change (6 : Nat) < 4 at hlt
    omega
  · change (6 : Nat) < 5 at hlt
    omega
  · change (6 : Nat) < 6 at hlt
    omega
  · exact sourceCoefficient_triple_2_6_7
  · exact sourceCoefficient_triple_2_6_8
  · exact sourceCoefficient_triple_2_6_9
end QEC.Coding.Why24AppendixANF
