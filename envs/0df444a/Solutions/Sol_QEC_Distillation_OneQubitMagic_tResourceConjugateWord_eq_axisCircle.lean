-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tResourceConjugateWord_eq_axisCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:03:29.696969+00:00
-- url     : https://prove2.me/submissions/427cc4aa-d7b7-4a62-a4c0-71bf820283d1

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_tResourceAxis_transport
import Theorems.Thm_QEC_Distillation_axisCircle_conjugate


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    tResourceConjugateWord =
      axisCircle tResourceConjugateAxis
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) := by
  rw [tResourceConjugateWord, tResourceAxisWord_eq_axisCircle]
  exact axisCircle_conjugate phaseGate tResourceAxis tResourceConjugateAxis
    phaseGate_tResourceAxis_transport _
end QEC.Distillation.OneQubitMagic
