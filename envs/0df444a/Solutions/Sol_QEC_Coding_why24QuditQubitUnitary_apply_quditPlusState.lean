-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitUnitary_apply_quditPlusState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:45:38.175074+00:00
-- url     : https://prove2.me/submissions/721f4e6e-abf8-441a-8e09-62da0e5d96a7

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    why24QuditQubitUnitary why24QuditPlusState = why24QubitPlusState :=
  rfl
end QEC.Coding
