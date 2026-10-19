-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/96344b97-bac3-44ea-81c5-077a3835444f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_iterate_dist_le_geometric
import Theorems.Thm_SoficGroups_ejThreeResidual_spectral_gap_of_pair_angles

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
    [∀ i j : Fin 3, (V i ⊓ V j).HasOrthogonalProjection]
    (c : ℝ) (hc : 0 ≤ c) (hchalf : c < (1 / 2 : ℝ))
    (hangle : ∀ (i j : Fin 3) (u v : H),
      u ∈ V i → u ∈ (V i ⊓ V j)ᗮ →
      v ∈ V j → v ∈ (V i ⊓ V j)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - (1 - 2 * c) / 6) ^ n := by
  have hc' : c ≤ 1 := by linarith
  apply ejThreeProjectionAverage_iterate_dist_le_geometric V
    (1 - 2 * c) (by linarith)
  intro y
  exact ejThreeResidual_spectral_gap_of_pair_angles
    V c hc hc' hangle y
end SoficGroups
