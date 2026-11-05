-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup.dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T11:06:39.479216+00:00
-- url     : https://prove2.me/submissions/b4f06a78-4f7e-4382-b3b3-f8e23e650ff8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryPrefixSetup

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution (m j : ℕ) :
    N m j=fixedLength (j*m) ∧ T m j=bankCut m j ∧ T m j≤ 2740*N m j := by
  unfold N T fixedLength bankCut
  constructor
  · rfl
  constructor
  · ring
  · omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalPrefixSetup
