-- Prove2me | solution 1 for SoficGroups.ejTwoResidualEnergy_ge_of_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/684b2045-b207-4a22-9610-2f7afe22e03b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejTwoProjection_norm_sq_sum_le_of_angle

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c)
    (hangle : ∀ (u v : H),
      u ∈ U → u ∈ (U ⊓ V)ᗮ →
      v ∈ V → v ∈ (U ⊓ V)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (w : H) (hw : w ∈ (U ⊓ V)ᗮ) :
    (1 - c) * ‖w‖ ^ 2 ≤
      ‖ejResidualProjection U w‖ ^ 2 +
        ‖ejResidualProjection V w‖ ^ 2 := by
  have hU := U.norm_sq_eq_add_norm_sq_starProjection w
  have hV := V.norm_sq_eq_add_norm_sq_starProjection w
  change ‖w‖ ^ 2 =
    ‖U.starProjection w‖ ^ 2 +
      ‖ejResidualProjection U w‖ ^ 2 at hU
  change ‖w‖ ^ 2 =
    ‖V.starProjection w‖ ^ 2 +
      ‖ejResidualProjection V w‖ ^ 2 at hV
  have hsum :=
    ejTwoProjection_norm_sq_sum_le_of_angle U V c hc hangle w hw
  nlinarith
end SoficGroups
