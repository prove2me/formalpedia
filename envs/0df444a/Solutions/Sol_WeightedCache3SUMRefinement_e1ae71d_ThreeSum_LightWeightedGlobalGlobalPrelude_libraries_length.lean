-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude.libraries_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:37:28.115884+00:00
-- url     : https://prove2.me/submissions/0de44eb3-d607-4ab5-8739-8a42ba8ebc58

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightExtensionBackendSetup
import Definitions.Def_Submission_ThreeSum_LightScales
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryGlobalPrelude

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude
open Light
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude
theorem _root_.solution (M b p K : ℕ) : (libraries M b p K).length=49 := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalGlobalPrelude
