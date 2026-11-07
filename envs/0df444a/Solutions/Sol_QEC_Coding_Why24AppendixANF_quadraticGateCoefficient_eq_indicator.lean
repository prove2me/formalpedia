-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.quadraticGateCoefficient_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:38:01.664301+00:00
-- url     : https://prove2.me/submissions/57541fd8-3d48-4964-9f02-617ce4991e2f

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution (pair : Fin 10 × Fin 10) :
    quadraticGateCoefficient pair.1 pair.2 =
      if pair ∈ quadraticGatePairs then 1 else 0 := rfl
end QEC.Coding.Why24AppendixANF
