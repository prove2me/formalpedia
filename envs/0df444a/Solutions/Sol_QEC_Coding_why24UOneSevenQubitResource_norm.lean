-- Prove2me | solution 1 for QEC.Coding.why24UOneSevenQubitResource_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:45:42.968231+00:00
-- url     : https://prove2.me/submissions/8cd69141-9922-4302-bc8c-bf00801305ed

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Theorems.Thm_QEC_Coding_why24UOneSevenQuditResource_norm
import Theorems.Thm_QEC_Coding_why24QuditQubitUnitary_apply_uOneSevenQuditResource

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : ‖why24UOneSevenQubitResource‖ = 1 := by
  rw [← why24QuditQubitUnitary_apply_uOneSevenQuditResource]
  change ‖why24QuditQubitUnitary.toLinearIsometryEquiv
    why24UOneSevenQuditResource‖ = 1
  rw [why24QuditQubitUnitary.toLinearIsometryEquiv.norm_map]
  exact why24UOneSevenQuditResource_norm
end QEC.Coding
