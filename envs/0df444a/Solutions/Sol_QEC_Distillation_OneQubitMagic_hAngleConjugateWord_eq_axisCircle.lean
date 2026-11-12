-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hAngleConjugateWord_eq_axisCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:21:51.977522+00:00
-- url     : https://prove2.me/submissions/6b543ff7-7ed4-48da-8f51-c6fca15df6b4

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_conjugates_hAngleAxis
import Theorems.Thm_QEC_Distillation_axisCircle_conjugate


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    hAngleConjugateWord = axisCircle hAngleConjugateAxis
      (hAngle : AddCircle (2 * Real.pi)) := by
  rw [hAngleConjugateWord, hAngleWord_eq_axisCircle]
  exact axisCircle_conjugate phaseGate hAngleAxis hAngleConjugateAxis
    phaseGate_conjugates_hAngleAxis _
end QEC.Distillation.OneQubitMagic
