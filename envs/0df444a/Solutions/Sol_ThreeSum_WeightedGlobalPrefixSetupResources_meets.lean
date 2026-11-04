-- Prove2me | solution 1 for ThreeSum.WeightedGlobalPrefixSetupResources.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:06:42.374197+00:00
-- url     : https://prove2.me/submissions/440bfac9-2d39-4abb-8096-99def3d356b1

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Definitions.Def_Submission_Weighted_Global_FrontendResources
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSetupResources
import Theorems.Thm_ThreeSum_WeightedGlobalPrefixSetupResources_need_ok
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_allocated_program_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrefixSetupResources
open Light LightWeightedGlobalPrefixSetup StageBounds WeightedGlobalCoverScale
open WeightedGlobalFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedGlobalPrefixSetupResources
theorem _root_.solution {lim : Limits} {m j F free d : ℕ} (μ : ℕ→ ℤ)
    (H : (need m j F).Ok lim free d) :
    Meets lim LightWeightedGlobalPrefixSetup.allocatedProgram 5 d [j,m,F,free] μ
      (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((WeightedAddresses.codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        LightSubsetAddress.Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) := by
  obtain ⟨hs,hw,hd⟩:= need_ok H
  exact allocated_program_meets μ H.space hs hw hd
end ThreeSum.WeightedGlobalPrefixSetupResources
