-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_left_8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:43:24.9428+00:00
-- url     : https://prove2.me/submissions/0074d4f2-3980-4ce8-94c3-89a92f14b5ab

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartD
import Theorems.Thm_QEC_Coding_Why24AppendixANF_sourceCoefficient_pair_8_9

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (right : Fin 10)
    (hlt : (8 : Fin 10) < right) :
    sourcePairCoefficient 8 right = quadraticGateCoefficient 8 right := by
  fin_cases right
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
  · exact sourceCoefficient_pair_8_9
end QEC.Coding.Why24AppendixANF
