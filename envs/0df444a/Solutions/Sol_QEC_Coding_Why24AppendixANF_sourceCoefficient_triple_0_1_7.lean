-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_1_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:42:11.42221+00:00
-- url     : https://prove2.me/submissions/8aed7052-a915-4115-9495-5d09f502790e

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Probe
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part00

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 1 7 = cubicGateCoefficient 0 1 7 := by
  decide
end QEC.Coding.Why24AppendixANF
