-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_5_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:13:02.081057+00:00
-- url     : https://prove2.me/submissions/bd563071-abea-4a3d-820d-52f583e75af3

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part15
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_5_7_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_5_7_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (7 : Fin 10) < third) :
    sourceTripleCoefficient 5 7 third = cubicGateCoefficient 5 7 third := by
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
  · exact sourceCoefficient_triple_5_7_8
  · exact sourceCoefficient_triple_5_7_9
end QEC.Coding.Why24AppendixANF
