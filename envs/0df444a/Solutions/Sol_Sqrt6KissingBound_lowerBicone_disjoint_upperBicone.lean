-- Prove2me | solution 1 for Sqrt6KissingBound.lowerBicone_disjoint_upperBicone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:19:06.463801+00:00
-- url     : https://prove2.me/submissions/7f19cc7b-a837-43ad-bea0-ef704f14c420

import Definitions.Def_Sqrt6KissingBound_StandardGeometry
import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_BiconeGeometry

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory
namespace Sqrt6KissingBound
theorem _root_.solution (k : ℕ) :
    Disjoint (lowerBicone k) (upperBicone k) := by
  rw [Set.disjoint_left]
  intro y hyl hyu
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo 0 a_bg) (fun t => t / s3_bg) at hyl
  change (standardCoordinates (k + 1)).symm y ∈
    profileRegion (k + 1) (Set.Ioo a_bg 1)
      (fun t => upperSlope_bg * (1 - t)) at hyu
  rcases hyl with ⟨hl, -⟩
  rcases hyu with ⟨hu, -⟩
  exact lt_asymm hl.2 hu.1
end Sqrt6KissingBound
