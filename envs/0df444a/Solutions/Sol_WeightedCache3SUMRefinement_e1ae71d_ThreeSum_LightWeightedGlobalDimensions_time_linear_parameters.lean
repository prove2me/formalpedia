-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.time_linear_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:42:21.813016+00:00
-- url     : https://prove2.me/submissions/677a8c86-97db-4521-8e2d-46a803ac04dd

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsTime
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
open WeightedGlobalSignedPadding TernaryExtensionEncoding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
theorem _root_.solution (M b p K n U : ℕ) :
    time M b p K n U ≤ 1000*(p^(dim M b p K n U)+dim M b p K n U+J M b n U+3) := by
  have hJ : J M b n U=Nat.clog b (4*U+1)+r M n+1 := rfl
  have hdim : Nat.clog p (8*(J M b n U+3)*p^(4*K))=dim M b p K n U := by
    unfold dim menuDegree
    congr 1
  unfold time LightWeightedGlobalDigitLength.clogTime LightWeightedGlobalDigitLength.time LightNatPower.time
  change 20*r M n+20+(20*Nat.clog b (4*U+1)+20+60)+
    (20*Nat.clog p (8*(J M b n U+3)*p^(4*K))+20)+(20*dim M b p K n U+20)+250 ≤ _
  rw [hdim]
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
