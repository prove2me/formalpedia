-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePairMoments.support_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:59:08.930086+00:00
-- url     : https://prove2.me/submissions/c1929b91-ad42-4ff3-a654-1697d6dca9c4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators
namespace ThreeSum.WeightedGlobalNativePairMoments
theorem _root_.solution {P : Type*} [Fintype P] (mode : P→ℤ) :
    TernaryPhysicalMomentSupport.support mode=TernaryPairedSupport.physicalSupport mode := rfl
end ThreeSum.WeightedGlobalNativePairMoments
