-- Prove2me | solution 1 for SoficGroups.ejThreeResidualMap_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/d2a1e78f-d1c3-44af-8e42-f4de3cb00867

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_norm_add_three_sq_le_three_mul

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
    ‖ejThreeResidualMap V x‖ ^ 2 ≤
      3 * ejThreeResidualEnergy V x := by
  simpa [ejThreeResidualMap_apply, ejThreeResidualEnergy] using
    norm_add_three_sq_le_three_mul
      (ejResidualProjection (V 0) x)
      (ejResidualProjection (V 1) x)
      (ejResidualProjection (V 2) x)
end SoficGroups
