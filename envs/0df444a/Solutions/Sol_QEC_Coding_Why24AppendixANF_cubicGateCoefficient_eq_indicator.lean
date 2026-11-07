-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.cubicGateCoefficient_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:38:46.4788+00:00
-- url     : https://prove2.me/submissions/1cc0c939-5afd-4858-ba1a-a7d1da53f326

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution
    (triple : Fin 10 × Fin 10 × Fin 10) :
    cubicGateCoefficient triple.1 triple.2.1 triple.2.2 =
      if triple ∈ cubicGateTriples then 1 else 0 := rfl
end QEC.Coding.Why24AppendixANF
