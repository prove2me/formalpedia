-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof.arenaFree_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:54:30.555547+00:00
-- url     : https://prove2.me/submissions/c88db12c-573e-4e2d-b286-ff4524f81d80

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryColorPreparationProof

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof
theorem _root_.solution (free n W J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    arenaFree free n W a b c J U≤arenaFree free n W n n n J U :=by
  have hb':=Nat.mul_le_mul_right (J+2) hb
  have hc':=Nat.mul_le_mul_right (J+2) hc
  have ha':=Nat.mul_le_mul_right (2^J) ha
  have ha'':=Nat.mul_le_mul_right (J+2) ha'
  unfold arenaFree work oMatrix positions carry cMatrix bMatrix
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalColorPreparationProof
