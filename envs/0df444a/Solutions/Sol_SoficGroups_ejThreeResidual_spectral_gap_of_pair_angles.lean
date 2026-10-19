-- Prove2me | solution 1 for SoficGroups.ejThreeResidual_spectral_gap_of_pair_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/4d6d4c7c-5031-495f-a32b-d1afb833d93f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualMap_spectral_gap
import Theorems.Thm_SoficGroups_ejTwoResidual_spectral_gap_of_angle

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
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1)
    (hangle : ∀ (i j : Fin 3) (u v : H),
      u ∈ V i → u ∈ (V i ⊓ V j)ᗮ →
      v ∈ V j → v ∈ (V i ⊓ V j)ᗮ →
        ‖inner ℂ u v‖ ≤ c * ‖u‖ * ‖v‖)
    (x : H) :
    (1 - 2 * c) * ejThreeResidualEnergy V x ≤
      ‖ejThreeResidualMap V x‖ ^ 2 := by
  apply ejThreeResidualMap_spectral_gap V x c
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 0) (V 1) c hc hc' (hangle 0 1) x
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 1) (V 2) c hc hc' (hangle 1 2) x
  · exact ejTwoResidual_spectral_gap_of_angle
      (V 2) (V 0) c hc hc' (hangle 2 0) x
end SoficGroups
