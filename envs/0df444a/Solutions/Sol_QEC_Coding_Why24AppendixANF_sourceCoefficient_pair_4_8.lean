-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_4_8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:18.42349+00:00
-- url     : https://prove2.me/submissions/7895be5f-c50b-4193-b32a-7dd0a72a84ce

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourcePairCoefficient 4 8 = quadraticGateCoefficient 4 8 := by
  decide
end QEC.Coding.Why24AppendixANF
