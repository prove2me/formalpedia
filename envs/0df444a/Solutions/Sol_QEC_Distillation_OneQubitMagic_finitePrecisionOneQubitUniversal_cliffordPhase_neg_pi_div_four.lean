-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.finitePrecisionOneQubitUniversal_cliffordPhase_neg_pi_div_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:21:42.325761+00:00
-- url     : https://prove2.me/submissions/325fc8c6-249d-4882-9691-de93154c5241

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_HAngleUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleConjugateWord_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleConjugateWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngleAxis_nonparallel
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hAngle_div_two_pi_irrational
import Theorems.Thm_QEC_Distillation_finitePrecisionOneQubitUniversal_of_irrational_axis_words


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    FinitePrecisionOneQubitUniversal
      (cliffordPhaseGenerators (-Real.pi / 4)) :=
  finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (cliffordPhaseGenerators (-Real.pi / 4))
    hAngleAxis hAngleConjugateAxis hAngle hAngleWord hAngleConjugateWord
    hAngleWord_mem_generated hAngleWord_eq_axisCircle
    hAngleConjugateWord_mem_generated hAngleConjugateWord_eq_axisCircle
    hAngle_div_two_pi_irrational hAngleAxis_nonparallel
end QEC.Distillation.OneQubitMagic
