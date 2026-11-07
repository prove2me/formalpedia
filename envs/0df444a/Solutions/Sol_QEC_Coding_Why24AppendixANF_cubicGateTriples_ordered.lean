-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.cubicGateTriples_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:38:12.572261+00:00
-- url     : https://prove2.me/submissions/6eb2bfac-3555-48da-a1e7-1838d3cdd866

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (triple : Fin 10 × Fin 10 × Fin 10)
    (htriple : triple ∈ cubicGateTriples) :
    triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2 := by
  have hall : cubicGateTriples.all (fun triple =>
      decide (triple.1 < triple.2.1 ∧ triple.2.1 < triple.2.2)) = true := by
    set_option maxRecDepth 2048 in decide
  exact of_decide_eq_true ((List.all_eq_true.mp hall) triple htriple)
end QEC.Coding.Why24AppendixANF
