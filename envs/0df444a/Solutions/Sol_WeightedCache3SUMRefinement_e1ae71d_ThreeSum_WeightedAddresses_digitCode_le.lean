-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses.digitCode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:07:51.710858+00:00
-- url     : https://prove2.me/submissions/7c3242ef-3c8c-49dc-8f03-6d2cc1d5673e

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Enumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
theorem _root_.solution {d : ℕ} (hd : d < 3) : digitCode d ≤ 3 := by
  unfold digitCode
  split <;> omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedAddresses
