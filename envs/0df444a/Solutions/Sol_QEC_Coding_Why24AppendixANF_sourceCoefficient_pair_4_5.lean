-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_4_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:05.545264+00:00
-- url     : https://prove2.me/submissions/e1aebe98-6ef4-4458-8cd5-6041749e2d4a

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourcePairCoefficient 4 5 = quadraticGateCoefficient 4 5 := by
  decide
end QEC.Coding.Why24AppendixANF
