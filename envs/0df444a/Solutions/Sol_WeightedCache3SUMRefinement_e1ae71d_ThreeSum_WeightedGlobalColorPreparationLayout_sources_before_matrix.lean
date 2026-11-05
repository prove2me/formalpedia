-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.sources_before_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:46:37.621401+00:00
-- url     : https://prove2.me/submissions/cb1ba27f-2612-4d6b-952f-9a1db09cb93d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
open LightWeightedGlobalColorPreparation
set_option maxHeartbeats 1000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
theorem _root_.solution (free n W : ℕ) :
    LightTernaryColorPrelude.av free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.bv free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.cv free n+n≤bMatrix free n W := by
  unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
    LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
    LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 bMatrix headerAt
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
