-- Prove2me | solution 1 for ThreeSum.WeightedFrozenQueryCost.cost_update_drop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:13.022459+00:00
-- url     : https://prove2.me/submissions/ff078f83-9373-4f28-8af1-1c6142191362

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_cost_update_loss

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration
namespace ThreeSum.WeightedFrozenQueryCost
theorem _root_.solution {N : ℕ} (R : Word N) (i : Fin N) (d : Fin 3)
    (hd : d≤R i) :
    cacheCost (Function.update R i d)=cacheCost R-(digitCost (R i).val-digitCost d.val) := by
  have hh := cost_update_loss R i d hd
  omega
end ThreeSum.WeightedFrozenQueryCost
