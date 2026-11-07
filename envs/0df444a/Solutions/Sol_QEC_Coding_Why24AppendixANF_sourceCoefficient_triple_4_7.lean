-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:12:55.056369+00:00
-- url     : https://prove2.me/submissions/91761aa7-8c5d-4200-b10b-2ed4a56bd161

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_7_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_7_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 4 7 third = cubicGateCoefficient 4 7 third := by
  fin_cases third
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
  · exact sourceCoefficient_triple_4_7_8
  · exact sourceCoefficient_triple_4_7_9
end QEC.Coding.Why24AppendixANF
