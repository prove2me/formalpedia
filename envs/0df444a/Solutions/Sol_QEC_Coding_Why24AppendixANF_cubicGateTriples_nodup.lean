-- Prove2me | solution 1 for QEC.Coding.Why24AppendixANF.cubicGateTriples_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:38:11.128107+00:00
-- url     : https://prove2.me/submissions/8d851321-b51f-49e4-8f87-5d17dae8ad3e

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Target
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ListStructure

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.Why24AppendixANF
open scoped BigOperators
namespace QEC.Coding.Why24AppendixANF
theorem _root_.solution : cubicGateTriples.Nodup := by
  set_option maxRecDepth 2048 in decide
end QEC.Coding.Why24AppendixANF
