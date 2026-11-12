-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tResourceConjugateWord_mem_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:10:30.55195+00:00
-- url     : https://prove2.me/submissions/bbb2f231-91df-48f3-b80d-6acefc5d89de

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_cliffordPhaseGenerators_conjugate_mem
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_mem_generated


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    tResourceConjugateWord ∈
      generatedUnitarySubgroup (cliffordPhaseGenerators tResourcePhaseAngle) := by
  exact cliffordPhaseGenerators_conjugate_mem tResourcePhaseAngle
    (phaseGate_mem_generated tResourcePhaseAngle)
    tResourceAxisWord_mem_generated
end QEC.Distillation.OneQubitMagic
