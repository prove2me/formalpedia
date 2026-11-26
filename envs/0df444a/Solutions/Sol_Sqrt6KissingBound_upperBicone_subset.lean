-- Prove2me | solution 1 for Sqrt6KissingBound.upperBicone_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:20:14.255364+00:00
-- url     : https://prove2.me/submissions/6d9bce6c-0c36-4c2c-a5c9-06c052569b5e

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry
import Theorems.Thm_Sqrt6KissingBound_upper_point_mem_cone_ball
import Theorems.Thm_Sqrt6KissingBound_inner_standardAxis_standardCoordinates
import Theorems.Thm_Sqrt6KissingBound_mem_tailBall
import Theorems.Thm_Sqrt6KissingBound_norm_standardAxis
attribute [local simp] Sqrt6KissingBound.inner_standardAxis_standardCoordinates
attribute [local simp] Sqrt6KissingBound.mem_tailBall
attribute [local simp] Sqrt6KissingBound.norm_standardAxis



set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    upperBicone k ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1 := by
  intro y hy
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo a_bg 1)
      (fun t => upperSlope_bg * (1 - t)) at hy
  let p := (standardCoordinates (k + 1)).symm y
  change p ∈ profileRegion (k + 1) (Set.Ioo a_bg 1)
    (fun t => upperSlope_bg * (1 - t)) at hy
  rcases hy with ⟨ht, hv⟩
  have hpoint := upper_point_mem_cone_ball k ht.1 ht.2 hv
  simpa [p] using hpoint
end Sqrt6KissingBound
