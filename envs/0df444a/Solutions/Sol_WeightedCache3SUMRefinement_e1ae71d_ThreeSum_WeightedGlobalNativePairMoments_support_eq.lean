-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments.support_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:19:03.164605+00:00
-- url     : https://prove2.me/submissions/1d3a096f-61ff-4388-a43c-416a8e18b1e0

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
theorem _root_.solution {P : Type*} [Fintype P] (mode : P→ℤ) :
    TernaryPhysicalMomentSupport.support mode=TernaryPairedSupport.physicalSupport mode := rfl
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairMoments
