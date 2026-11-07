-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:10:31.397094+00:00
-- url     : https://prove2.me/submissions/fdcbddc7-fa07-4d7c-b789-11f38b943a86

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_triple_0_1_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (third : Fin 10)
    (hlt : (1 : Fin 10) < third) :
    sourceTripleCoefficient 0 1 third = cubicGateCoefficient 0 1 third := by
  fin_cases third
  · change (1 : Nat) < 0 at hlt
    omega
  · change (1 : Nat) < 1 at hlt
    omega
  · exact sourceCoefficient_triple_0_1_2
  · exact sourceCoefficient_triple_0_1_3
  · exact sourceCoefficient_triple_0_1_4
  · exact sourceCoefficient_triple_0_1_5
  · exact sourceCoefficient_triple_0_1_6
  · exact sourceCoefficient_triple_0_1_7
  · exact sourceCoefficient_triple_0_1_8
  · exact sourceCoefficient_triple_0_1_9
end QEC.Coding.Why24AppendixANF
