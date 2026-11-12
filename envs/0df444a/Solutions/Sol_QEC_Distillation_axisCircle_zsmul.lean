-- Prove2me | solution 1 for QEC.Distillation.axisCircle_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:16:44.532993+00:00
-- url     : https://prove2.me/submissions/1948f485-1de9-496d-823b-46d48db7b78d

import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution (axis : UnitBlochAxis) (t : AddCircle (2 * Real.pi)) (z : Int) :
    axisCircle axis (z • t) = (axisCircle axis t) ^ z := by
  exact map_zsmul (axisCircleAddHom axis) z t
end QEC.Distillation
