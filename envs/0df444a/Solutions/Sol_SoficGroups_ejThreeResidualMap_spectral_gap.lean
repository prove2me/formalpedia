-- Prove2me | solution 1 for SoficGroups.ejThreeResidualMap_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/c2355c04-e4c3-438c-9109-a3e3b283d02f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_three_pairwise_residual_spectral_gap

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution (x : H) (ε : ℝ)
    (h01 : (1 - ε) *
      (‖ejResidualProjection (V 0) x‖ ^ 2 +
        ‖ejResidualProjection (V 1) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 0) x +
        ejResidualProjection (V 1) x‖ ^ 2)
    (h12 : (1 - ε) *
      (‖ejResidualProjection (V 1) x‖ ^ 2 +
        ‖ejResidualProjection (V 2) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 1) x +
        ejResidualProjection (V 2) x‖ ^ 2)
    (h20 : (1 - ε) *
      (‖ejResidualProjection (V 2) x‖ ^ 2 +
        ‖ejResidualProjection (V 0) x‖ ^ 2) ≤
      ‖ejResidualProjection (V 2) x +
        ejResidualProjection (V 0) x‖ ^ 2) :
    (1 - 2 * ε) * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  exact three_pairwise_residual_spectral_gap
    (ejResidualProjection (V 0) x)
    (ejResidualProjection (V 1) x)
    (ejResidualProjection (V 2) x)
    ε h01 h12 h20
end SoficGroups
