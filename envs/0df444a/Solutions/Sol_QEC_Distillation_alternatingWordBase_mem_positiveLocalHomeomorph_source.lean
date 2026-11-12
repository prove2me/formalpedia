-- Prove2me | solution 1 for QEC.Distillation.alternatingWordBase_mem_positiveLocalHomeomorph_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:21:03.092258+00:00
-- url     : https://prove2.me/submissions/f521d4f1-01eb-462f-911b-dab1a7f1255c

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_alternatingWordBase_mem_localHomeomorph_source
import Theorems.Thm_QEC_Distillation_alternatingWordBase_mem_positiveSet

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
theorem _root_.solution
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis') :
    alternatingWordBase ∈
      (alternatingWordPositiveLocalHomeomorph axis axis' hnonparallel).source := by
  rw [alternatingWordPositiveLocalHomeomorph,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨alternatingWordBase_mem_localHomeomorph_source axis axis' hnonparallel,
    alternatingWordBase_mem_positiveSet axis axis'⟩
end QEC.Distillation
