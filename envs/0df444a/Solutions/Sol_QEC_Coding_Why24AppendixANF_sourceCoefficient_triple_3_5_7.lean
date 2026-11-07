-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_3_5_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:52:02.919769+00:00
-- url     : https://prove2.me/submissions/3596d690-0a30-411d-8553-c71eecb3f3d1

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part12

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 3 5 7 = cubicGateCoefficient 3 5 7 := by
  decide
end QEC.Coding.Why24AppendixANF
