-- Prove2me | solution 1 for QEC.Distillation.UnitBlochAxis.nonparallel_crossSq_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:13:58.303648+00:00
-- url     : https://prove2.me/submissions/b28a8b7c-a6f5-43f3-a2d5-6d867d4ec31e

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
namespace UnitBlochAxis
theorem _root_.solution {axis axis' : UnitBlochAxis}
    (h : axis.Nonparallel axis') : blochCrossSq axis axis' ≠ 0 := by
  exact ne_of_gt h
end UnitBlochAxis
end QEC.Distillation
