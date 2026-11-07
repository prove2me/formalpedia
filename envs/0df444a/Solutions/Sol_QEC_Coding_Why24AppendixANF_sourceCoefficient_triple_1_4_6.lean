-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_1_4_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:48:20.516438+00:00
-- url     : https://prove2.me/submissions/45b3486c-d7d0-4d77-8d7d-32e23758d8af

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part07

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 1 4 6 = cubicGateCoefficient 1 4 6 := by
  decide
end QEC.Coding.Why24AppendixANF
