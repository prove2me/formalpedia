-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:53.773488+00:00
-- url     : https://prove2.me/submissions/1960c5c6-f73a-444b-a173-94d6c8bcdd63

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_7_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_7_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 0 7 third = cubicGateCoefficient 0 7 third := by
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
  · exact sourceCoefficient_triple_0_7_8
  · exact sourceCoefficient_triple_0_7_9
end QEC.Coding.Why24AppendixANF
