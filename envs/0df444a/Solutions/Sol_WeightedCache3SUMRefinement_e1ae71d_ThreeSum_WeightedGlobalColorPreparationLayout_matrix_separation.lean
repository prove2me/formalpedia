-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout.matrix_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:49:45.651317+00:00
-- url     : https://prove2.me/submissions/d3539be3-fe02-439e-861a-ff312ed2cc05

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
    bMatrix free n W+nB*(J+2)=cMatrix free n W nB J ∧
    cMatrix free n W nB J+nC*(J+2)=carry free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)=positions free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J=oMatrix free n W nA nB nC J :=
  ⟨rfl,rfl,rfl,rfl⟩
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColorPreparationLayout
