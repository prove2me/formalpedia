-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:42.266266+00:00
-- url     : https://prove2.me/submissions/a7457660-2e76-4114-ba8f-6d36a48370ad

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_3_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (3 : Fin 10) < third) :
    sourceTripleCoefficient 0 3 third = cubicGateCoefficient 0 3 third := by
  fin_cases third
  · change (3 : Nat) < 0 at hlt
    omega
  · change (3 : Nat) < 1 at hlt
    omega
  · change (3 : Nat) < 2 at hlt
    omega
  · change (3 : Nat) < 3 at hlt
    omega
  · exact sourceCoefficient_triple_0_3_4
  · exact sourceCoefficient_triple_0_3_5
  · exact sourceCoefficient_triple_0_3_6
  · exact sourceCoefficient_triple_0_3_7
  · exact sourceCoefficient_triple_0_3_8
  · exact sourceCoefficient_triple_0_3_9
end QEC.Coding.Why24AppendixANF
