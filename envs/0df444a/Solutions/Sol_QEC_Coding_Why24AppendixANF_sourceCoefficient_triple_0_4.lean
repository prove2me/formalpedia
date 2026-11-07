-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:45.146197+00:00
-- url     : https://prove2.me/submissions/da29e702-7f0e-43c0-b664-496781eaff29

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part03
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_4_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_4_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_4_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_4_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_4_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (4 : Fin 10) < third) :
    sourceTripleCoefficient 0 4 third = cubicGateCoefficient 0 4 third := by
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
  · exact sourceCoefficient_triple_0_4_5
  · exact sourceCoefficient_triple_0_4_6
  · exact sourceCoefficient_triple_0_4_7
  · exact sourceCoefficient_triple_0_4_8
  · exact sourceCoefficient_triple_0_4_9
end QEC.Coding.Why24AppendixANF
