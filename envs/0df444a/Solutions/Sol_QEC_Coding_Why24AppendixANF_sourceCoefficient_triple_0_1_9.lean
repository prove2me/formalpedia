-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:42:42.978709+00:00
-- url     : https://prove2.me/submissions/8167c271-e3cd-42ed-80b3-27d1d055d3e8

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 1 9 = cubicGateCoefficient 0 1 9 := by
  decide
end QEC.Coding.Why24AppendixANF
