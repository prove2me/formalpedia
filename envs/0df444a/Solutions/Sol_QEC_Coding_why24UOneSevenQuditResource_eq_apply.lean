-- Prove2me | solution 1 for QEC.Coding.why24UOneSevenQuditResource_eq_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:45:41.365198+00:00
-- url     : https://prove2.me/submissions/22341a53-e47e-43e8-88e5-8dcf4f18d147

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    why24UOneSevenQuditResource = why24UOneSeven why24QuditPlusState :=
  rfl
end QEC.Coding
