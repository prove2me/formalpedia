-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.quadraticGatePairs_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:37:59.970504+00:00
-- url     : https://prove2.me/submissions/cbe2ab48-d419-47c6-9c00-110973418e69

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (pair : Fin 10 × Fin 10)
    (hpair : pair ∈ quadraticGatePairs) : pair.1 < pair.2 := by
  have hall :
      quadraticGatePairs.all (fun pair => decide (pair.1 < pair.2)) = true := by
    set_option maxRecDepth 2048 in decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) pair hpair)
end QEC.Coding.Why24AppendixANF
