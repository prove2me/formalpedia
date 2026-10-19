-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_dist_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/00a1844f-604d-4caa-adbc-cbd4b5e4dce2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualMap_norm_sq_le
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_dist_sq

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
    dist x (ejThreeProjectionAverage V x) ^ 2 ≤
      ejThreeResidualEnergy V x / 3 := by
  rw [ejThreeProjectionAverage_dist_sq]
  have h := ejThreeResidualMap_norm_sq_le V x
  nlinarith
end SoficGroups
