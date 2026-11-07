-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.sourceCoefficient_pair_4_9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:38.198711+00:00
-- url     : https://prove2.me/submissions/1438536d-39de-42b9-83f9-77379c29b5c1

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Quadratic_PartC

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
set_option maxRecDepth 2048
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution :
    sourcePairCoefficient 4 9 = quadraticGateCoefficient 4 9 := by
  decide
end QEC.Coding.Why24AppendixANF
