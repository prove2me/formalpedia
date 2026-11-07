-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:42:22.285203+00:00
-- url     : https://prove2.me/submissions/bc10ae20-8598-4f9d-a4f7-6e7eb3f9eddb

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 1 8 = cubicGateCoefficient 0 1 8 := by
  decide
end QEC.Coding.Why24AppendixANF
