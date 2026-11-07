-- Prove2me | solution 1 for QEC.Coding.why24AppendixReverseCorrectionPhase_add_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:40:51.164236+00:00
-- url     : https://prove2.me/submissions/c11d0320-549d-4678-a601-468a81aa50c3

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_Data
import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution
    (outcome : Why24AppendixReverseOutcome)
    (retained : Semantics.Qubit.Bitstring (Fin 3)) :
    why24AppendixReverseCorrectionPhase outcome retained +
        why24AppendixReverseSourcePhase outcome retained =
      why24CCZPhase retained := by
  rw [why24AppendixReverseCorrectionPhase]
  let source := why24AppendixReverseSourcePhase outcome retained
  let target := why24CCZPhase retained
  change (source + target) + source = target
  calc
    (source + target) + source = target + (source + source) := by
      rw [add_assoc, add_comm target source, ← add_assoc,
        add_comm (source + source) target]
    _ = target := by
      rw [CharTwo.add_self_eq_zero, add_zero]
end QEC.Coding
