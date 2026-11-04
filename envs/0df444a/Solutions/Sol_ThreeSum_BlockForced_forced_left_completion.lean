-- Prove2me | solution 1 for ThreeSum.BlockForced.forced_left_completion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:50.80868+00:00
-- url     : https://prove2.me/submissions/43094eab-a059-437a-b9eb-52ed4dadcb08

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Theorems.Thm_ThreeSum_BlockForced_forced_left_of_agreement

set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : prefixLeft I u ∪ residual I t = leftSubset t :=
  forced_left_of_agreement I u _ (Finset.mem_filter.mp ht).2.2
end ThreeSum.BlockForced
