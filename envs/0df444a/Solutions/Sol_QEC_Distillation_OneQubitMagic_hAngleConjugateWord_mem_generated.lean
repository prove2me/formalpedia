-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hAngleConjugateWord_mem_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:09:47.524968+00:00
-- url     : https://prove2.me/submissions/dc7d7b43-5646-4902-9f20-f46046d8768c

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_mem_generated
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
    hAngleConjugateWord ∈ generatedUnitarySubgroup
      (cliffordPhaseGenerators (-Real.pi / 4)) := by
  exact cliffordPhaseGenerators_conjugate_mem _
    (phaseGate_mem_generated _) hAngleWord_mem_generated
end QEC.Distillation.OneQubitMagic
