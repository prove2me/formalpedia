-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_2_8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:37:43.911072+00:00
-- url     : https://prove2.me/submissions/35aa7db1-065b-479a-89bc-467713987616

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartB

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourcePairCoefficient 2 8 = quadraticGateCoefficient 2 8 := by
  decide
end QEC.Coding.Why24AppendixANF
