-- Prove2me | solution 1 for QEC.Distillation.axisCircleSU_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:18:57.927638+00:00
-- url     : https://prove2.me/submissions/7c9ee272-f3ee-49bc-b277-529c3c2fa1dc

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Theorems.Thm_QEC_Distillation_axisCircle_zsmul

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircleSU axis (z • t) = (axisCircleSU axis t) ^ z := by
  apply Subtype.ext
  exact axisCircle_zsmul axis t z
end QEC.Distillation
