-- Prove2me | solution 1 for SoficGroups.ejThreeResidualEnergy_le_three_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/29290c29-4545-4e16-a213-e8995fc8ffb9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejResidualProjection_norm_le

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
    ejThreeResidualEnergy V x ≤ 3 * ‖x‖ ^ 2 := by
  have h0 : ‖ejResidualProjection (V 0) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 0 x)
  have h1 : ‖ejResidualProjection (V 1) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 1 x)
  have h2 : ‖ejResidualProjection (V 2) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (ejResidualProjection_norm_le V 2 x)
  unfold ejThreeResidualEnergy
  linarith
end SoficGroups
