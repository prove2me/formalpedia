-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.quadraticGatePairs_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:37:20.272288+00:00
-- url     : https://prove2.me/submissions/0c9decf4-e8a6-4800-ba36-4bc788b76d2f

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution : quadraticGatePairs.Nodup := by
  set_option maxRecDepth 2048 in decide
end QEC.Coding.Why24AppendixANF
