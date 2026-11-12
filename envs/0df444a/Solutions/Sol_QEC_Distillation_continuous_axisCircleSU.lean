-- Prove2me | solution 1 for QEC.Distillation.continuous_axisCircleSU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:16:51.138325+00:00
-- url     : https://prove2.me/submissions/926b6a67-010e-4ea8-b28d-46551b78c222

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_axisCircle_continuous


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution (axis : UnitBlochAxis) :
    Continuous (axisCircleSU axis) := by
  apply continuous_induced_rng.2
  exact axisCircle_continuous axis
end QEC.Distillation
