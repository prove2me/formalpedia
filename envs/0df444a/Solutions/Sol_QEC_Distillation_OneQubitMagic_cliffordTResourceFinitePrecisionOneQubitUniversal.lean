-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.cliffordTResourceFinitePrecisionOneQubitUniversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:42:53.657945+00:00
-- url     : https://prove2.me/submissions/367a477c-4d2c-415c-b663-410ac90ba131

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisWord_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceConjugateWord_mem_generated
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceConjugateWord_eq_axisCircle
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxes_nonparallel
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisAngle_irrational
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
      (cliffordPhaseGenerators tResourcePhaseAngle) := by
  exact finitePrecisionOneQubitUniversal_of_irrational_axis_words
    (generators := cliffordPhaseGenerators tResourcePhaseAngle)
    (axis := tResourceAxis)
    (axis' := tResourceConjugateAxis)
    (theta := tResourceAxisAngle)
    (word := tResourceAxisWord)
    (word' := tResourceConjugateWord)
    tResourceAxisWord_mem_generated
    tResourceAxisWord_eq_axisCircle
    tResourceConjugateWord_mem_generated
    tResourceConjugateWord_eq_axisCircle
    tResourceAxisAngle_irrational
    tResourceAxes_nonparallel
end QEC.Distillation.OneQubitMagic
