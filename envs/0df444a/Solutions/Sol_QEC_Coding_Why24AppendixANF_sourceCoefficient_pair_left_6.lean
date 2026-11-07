-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:43:16.443385+00:00
-- url     : https://prove2.me/submissions/86a11390-d38f-4c58-9184-7f31adbc6d5f

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_6_7
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_6_8
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_6_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (6 : Fin 10) < right) :
    sourcePairCoefficient 6 right = quadraticGateCoefficient 6 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_6_7
  · exact sourceCoefficient_pair_6_8
  · exact sourceCoefficient_pair_6_9
end QEC.Coding.Why24AppendixANF
