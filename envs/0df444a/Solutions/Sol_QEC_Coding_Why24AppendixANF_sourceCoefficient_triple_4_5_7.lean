-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_4_5_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:53:25.632132+00:00
-- url     : https://prove2.me/submissions/9e4ce4b6-3ad5-4bea-9e57-20c716663673

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part14

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 4 5 7 = cubicGateCoefficient 4 5 7 := by
  decide
end QEC.Coding.Why24AppendixANF
