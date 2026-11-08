-- Prove2me | solution 1 for QEC.Coding.why24QubitPlusState_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:48:07.578594+00:00
-- url     : https://prove2.me/submissions/cfb86bc1-82ff-4fe5-a1c5-7a338fb1b77d

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Theorems.Thm_QEC_Coding_why24QuditPlusState_norm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : ‖why24QubitPlusState‖ = 1 := by
  change ‖why24QuditQubitUnitary.toLinearIsometryEquiv why24QuditPlusState‖ = 1
  rw [why24QuditQubitUnitary.toLinearIsometryEquiv.norm_map]
  exact why24QuditPlusState_norm
end QEC.Coding
