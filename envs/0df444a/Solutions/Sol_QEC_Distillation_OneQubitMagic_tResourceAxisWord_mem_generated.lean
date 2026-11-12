-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tResourceAxisWord_mem_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:07:10.763169+00:00
-- url     : https://prove2.me/submissions/ab3a1679-b2c8-4f68-875f-989f6f1b110f

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_cliffordPhaseGenerators_compose_mem
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_mem_generated


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    tResourceAxisWord ∈
      generatedUnitarySubgroup (cliffordPhaseGenerators tResourcePhaseAngle) := by
  repeat' apply cliffordPhaseGenerators_compose_mem
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle
  · exact hadamardGate_mem_generated tResourcePhaseAngle
  · exact phaseGate_mem_generated tResourcePhaseAngle
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle
  · exact hadamardGate_mem_generated tResourcePhaseAngle
  · exact phaseShiftGate_mem_generated tResourcePhaseAngle
end QEC.Distillation.OneQubitMagic
