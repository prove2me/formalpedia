-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_triple_0_3_6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:43:11.938975+00:00
-- url     : https://prove2.me/submissions/56885865-3d1a-4393-9747-c56968a3587e

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Cubic_Part02

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourceTripleCoefficient 0 3 6 = cubicGateCoefficient 0 3 6 := by
  decide
end QEC.Coding.Why24AppendixANF
