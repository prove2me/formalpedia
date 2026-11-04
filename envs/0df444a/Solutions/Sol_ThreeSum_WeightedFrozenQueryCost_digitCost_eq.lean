-- Prove2me | solution 1 for ThreeSum.WeightedFrozenQueryCost.digitCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:14:56.628837+00:00
-- url     : https://prove2.me/submissions/ebcc529e-c2ae-48b3-a5ee-dd648896d4b3

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution (d : Fin 3) : digitCost d.val = c d := by
  fin_cases d <;> norm_num [digitCost,c]
end ThreeSum.WeightedFrozenQueryCost
