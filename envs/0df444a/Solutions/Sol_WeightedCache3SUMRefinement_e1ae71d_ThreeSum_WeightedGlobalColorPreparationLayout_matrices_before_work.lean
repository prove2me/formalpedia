-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrices_before_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:59:08.85919+00:00
-- url     : https://prove2.me/submissions/c4371f24-7366-4c78-bb44-702f7fad7eed

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
theorem _root_.solution (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)≤work free n W nA nB nC J ∧
    cMatrix free n W nB J+nC*(J+2)≤work free n W nA nB nC J ∧
    oMatrix free n W nA nB nC J+nA*2^J*(J+2)≤work free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J≤work free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)≤work free n W nA nB nC J := by
  unfold work oMatrix positions carry cMatrix bMatrix
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
