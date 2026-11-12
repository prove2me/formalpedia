-- Prove2me | solution 1 for QEC.Distillation.closedSubgroup_eq_top_of_contains_nonparallel_axisCircles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:36:36.715683+00:00
-- url     : https://prove2.me/submissions/e9e214ba-c8d0-4b18-9d94-b30e516b0ca9

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Theorems.Thm_QEC_Distillation_subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
theorem _root_.solution
    (K : Subgroup SingleQubitSpecialUnitary)
    (_hclosed : IsClosed (K : Set SingleQubitSpecialUnitary))
    (axis axis' : UnitBlochAxis) (hnonparallel : axis.Nonparallel axis')
    (haxis : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis t ∈ K)
    (haxis' : ∀ t : AddCircle (2 * Real.pi), axisCircleSU axis' t ∈ K) :
    K = ⊤ := by
  apply top_unique
  intro U _
  exact subgroup_contains_all_specialUnitary_of_contains_nonparallel_axisCircles
    K axis axis' hnonparallel haxis haxis' U
end QEC.Distillation
