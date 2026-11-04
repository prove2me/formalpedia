-- Prove2me | solution 1 for ThreeSum.WantedPairs.pairs_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:04.276353+00:00
-- url     : https://prove2.me/submissions/549997f1-62f0-4e75-859e-0e5332965abb

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs

set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) :
    pairs μ offsets flat left 0=[] := rfl
end ThreeSum.WantedPairs
