-- Prove2me | solution 1 for QEC.Coding.why24AppendixReverseOutcome_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:45:36.709772+00:00
-- url     : https://prove2.me/submissions/d03364cc-4689-4b5d-9005-a64ac1c9344b

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    Fintype.card Why24AppendixReverseOutcome = 128 := by
  rw [Semantics.Qubit.card_bitstring]
  norm_num
end QEC.Coding
