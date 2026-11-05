-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration.digitCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:08:00.910599+00:00
-- url     : https://prove2.me/submissions/3bc407db-7682-47ca-915f-4337a26f873d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Addresses
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
theorem _root_.solution (d : Fin 3) : digitCost d.val = (![0,1369,2740] : Fin 3→ℕ) d := by
  fin_cases d <;> norm_num [digitCost]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankEnumeration
