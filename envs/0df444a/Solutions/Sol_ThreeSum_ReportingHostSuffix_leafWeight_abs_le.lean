-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.leafWeight_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:57.66622+00:00
-- url     : https://prove2.me/submissions/dfc18cb2-9ad2-4eed-a3c5-aef51c7acf65

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Theorems.Thm_ThreeSum_SignedLeaf_abs_value_le


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset sourceCut stage B D : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (hstage : stage ≤ W) (hL : (preL ∪ liftSet hfit S).card ≤ sourceCut)
    (hR : (preR ∪ liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) :
    |leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
  SignedLeaf.abs_value_le f g stage preL preR _ hstage hL hR hf hg
end ThreeSum.ReportingHostSuffix
