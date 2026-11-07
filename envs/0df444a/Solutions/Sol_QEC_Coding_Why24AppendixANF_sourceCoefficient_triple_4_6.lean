-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:12:50.367582+00:00
-- url     : https://prove2.me/submissions/be2297d5-4f84-45f7-bba6-5e728ede4ff0

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_6_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_6_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_4_6_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (6 : Fin 10) < third) :
    sourceTripleCoefficient 4 6 third = cubicGateCoefficient 4 6 third := by
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
  · exact sourceCoefficient_triple_4_6_7
  · exact sourceCoefficient_triple_4_6_8
  · exact sourceCoefficient_triple_4_6_9
end QEC.Coding.Why24AppendixANF
