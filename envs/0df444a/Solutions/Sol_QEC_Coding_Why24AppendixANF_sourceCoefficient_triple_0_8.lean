-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:54.866602+00:00
-- url     : https://prove2.me/submissions/b9d57e07-61ae-4b50-83d1-5cab03813e3d

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part04
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_8_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (8 : Fin 10) < third) :
    sourceTripleCoefficient 0 8 third = cubicGateCoefficient 0 8 third := by
  fin_cases third
  · change (8 : Nat) < 0 at hlt
    omega
  · change (8 : Nat) < 1 at hlt
    omega
  · change (8 : Nat) < 2 at hlt
    omega
  · change (8 : Nat) < 3 at hlt
    omega
  · change (8 : Nat) < 4 at hlt
    omega
  · change (8 : Nat) < 5 at hlt
    omega
  · change (8 : Nat) < 6 at hlt
    omega
  · change (8 : Nat) < 7 at hlt
    omega
  · change (8 : Nat) < 8 at hlt
    omega
  · exact sourceCoefficient_triple_0_8_9
end QEC.Coding.Why24AppendixANF
