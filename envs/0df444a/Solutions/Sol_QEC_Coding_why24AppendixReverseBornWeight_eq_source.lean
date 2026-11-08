-- Prove2me | solution 1 for QEC.Coding.why24AppendixReverseBornWeight_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:45:47.500949+00:00
-- url     : https://prove2.me/submissions/2965ad4f-4a09-4809-9930-049e581670aa

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
section
noncomputable section
namespace QEC.Coding
private theorem why24AppendixReverseRawBranch_eq_phaseUniform
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseRawBranch outcome =
      why24PhaseUniformRetainedBranch
        (why24AppendixReverseSourcePhase outcome) := by
  ext retained
  rw [why24AppendixReverseRawBranch_apply,
    why24PhaseUniformRetainedBranch_apply]
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution
    (outcome : Why24AppendixReverseOutcome) :
    why24AppendixReverseBornWeight outcome = (1 / 128 : Real) := by
  rw [why24AppendixReverseBornWeight,
    why24AppendixReverseRawBranch_eq_phaseUniform,
    why24PhaseUniformRetainedBranch_normSq]
end QEC.Coding
