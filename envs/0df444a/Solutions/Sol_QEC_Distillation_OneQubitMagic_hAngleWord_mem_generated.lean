-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hAngleWord_mem_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:06:18.114225+00:00
-- url     : https://prove2.me/submissions/29acf950-9e35-4d7e-9e74-5f3e2266fcb0

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
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
    hAngleWord ∈ generatedUnitarySubgroup
      (cliffordPhaseGenerators (-Real.pi / 4)) := by
  let G := generatedUnitarySubgroup (cliffordPhaseGenerators (-Real.pi / 4))
  have hH : hadamardGate ∈ G := hadamardGate_mem_generated _
  have hK : phaseGate ∈ G := phaseGate_mem_generated _
  have hP : phaseShiftGate (-Real.pi / 4) ∈ G := phaseShiftGate_mem_generated _
  exact G.mul_mem
    (G.mul_mem (G.pow_mem (G.mul_mem hH hK) 3)
      (G.pow_mem (G.mul_mem hH hP) 4)) hK
end QEC.Distillation.OneQubitMagic
