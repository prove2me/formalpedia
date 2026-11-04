-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColorPreparationLayout.sources_before_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:10:25.934376+00:00
-- url     : https://prove2.me/submissions/c1b205da-f6e8-48da-8bfe-d07d711895a5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution (free n W : ℕ) :
    LightTernaryColorPrelude.av free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.bv free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.cv free n+n≤bMatrix free n W := by
  unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
    LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
    LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 bMatrix headerAt
  omega
end ThreeSum.WeightedGlobalColorPreparationLayout
