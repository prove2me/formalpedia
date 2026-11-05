-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.prime_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:24:55.819781+00:00
-- url     : https://prove2.me/submissions/6ab22dfe-b0b1-4dec-9746-91f1c0cf99a9

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_LocalCoverBounds_selectedPrime_sq_lower


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (m : ℕ) : threshold m ≤ prime m^2 :=
  LocalCoverBounds.selectedPrime_sq_lower _
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
