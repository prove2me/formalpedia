-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/8ad3693a-b323-4f5a-9410-beecc4c33e84

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidual_cross_re_inner
import Theorems.Thm_SoficGroups_ejResidualProjection_average_norm_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (x : H) :
    ejThreeResidualEnergy V (ejThreeProjectionAverage V x) =
      ejThreeResidualEnergy V x -
        (2 / 3 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 +
        (1 / 9 : ℝ) *
          ejThreeResidualEnergy V (ejThreeResidualMap V x) := by
  unfold ejThreeResidualEnergy
  rw [ejThreeProjectionAverage_apply,
    ejResidualProjection_average_norm_sq (V 0),
    ejResidualProjection_average_norm_sq (V 1),
    ejResidualProjection_average_norm_sq (V 2)]
  have hcross := ejThreeResidual_cross_re_inner V x
  nlinarith
end SoficGroups
