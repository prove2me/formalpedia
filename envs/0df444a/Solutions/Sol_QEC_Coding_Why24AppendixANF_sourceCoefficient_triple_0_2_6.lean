-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_2_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:25:04.021868+00:00
-- url     : https://prove2.me/submissions/d2e2656c-4ffe-4ef6-afaf-6f3f4343539a

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part01

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 2 6 = cubicGateCoefficient 0 2 6 := by
  decide
end QEC.Coding.Why24AppendixANF
