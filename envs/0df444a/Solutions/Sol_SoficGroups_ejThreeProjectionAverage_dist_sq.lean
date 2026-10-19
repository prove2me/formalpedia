-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/02768281-f4dd-43e4-8bfd-b7c7d641e299

import Mathlib
import Definitions.Def_NonSoficGroup

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
    dist x (ejThreeProjectionAverage V x) ^ 2 =
      (1 / 9 : ℝ) * ‖ejThreeResidualMap V x‖ ^ 2 := by
  rw [dist_eq_norm, ejThreeProjectionAverage_apply]
  have hsub :
      x - (x - (3 : ℂ)⁻¹ • ejThreeResidualMap V x) =
        (3 : ℂ)⁻¹ • ejThreeResidualMap V x := by
    abel
  rw [hsub, norm_smul, norm_inv]
  norm_num
  ring
end SoficGroups
