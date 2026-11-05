-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale.scale_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:24:58.11078+00:00
-- url     : https://prove2.me/submissions/c110ba96-071b-4e78-83e5-285d01e1ed39

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (C c d : ℕ) : 0 < scale C c d := by unfold scale; positivity
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverScale
