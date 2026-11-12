-- Prove2me | solution 1 for QEC.Distillation.alternatingAxisWord_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:15:49.605733+00:00
-- url     : https://prove2.me/submissions/1ec17d12-2401-4d32-8db1-7996178805ae

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
theorem _root_.solution (K : Subgroup SingleQubitSpecialUnitary)
    (axis axis' : UnitBlochAxis)
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K)
    (x y z : Real) : alternatingAxisWord axis axis' x y z ∈ K := by
  apply K.mul_mem
  · apply K.mul_mem
    · exact haxis (x : AddCircle (2 * Real.pi))
    · exact haxis' (y : AddCircle (2 * Real.pi))
  · exact haxis (z : AddCircle (2 * Real.pi))
end QEC.Distillation
