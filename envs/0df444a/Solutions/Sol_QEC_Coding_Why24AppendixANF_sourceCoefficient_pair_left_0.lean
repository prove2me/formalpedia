-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:38:13.662103+00:00
-- url     : https://prove2.me/submissions/6ac770e2-2b93-4967-bb74-331d6bdb8898

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartA
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_1
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_2
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_3
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_4
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_5
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_6
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_0_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (0 : Fin 10) < right) :
    sourcePairCoefficient 0 right = quadraticGateCoefficient 0 right := by
  fin_cases right
  · change (0 : Nat) < 0 at hlt
    omega
  · exact sourceCoefficient_pair_0_1
  · exact sourceCoefficient_pair_0_2
  · exact sourceCoefficient_pair_0_3
  · exact sourceCoefficient_pair_0_4
  · exact sourceCoefficient_pair_0_5
  · exact sourceCoefficient_pair_0_6
  · exact sourceCoefficient_pair_0_7
  · exact sourceCoefficient_pair_0_8
  · exact sourceCoefficient_pair_0_9
end QEC.Coding.Why24AppendixANF
