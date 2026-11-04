-- Prove2me | solution 1 for ThreeSum.BlockForced.residual_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:08.426796+00:00
-- url     : https://prove2.me/submissions/ef35c111-b5a9-45f2-9038-3fe61088a865

import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Definitions.Def_Submission_ThreeSum_BlockForced
import Theorems.Thm_ThreeSum_BlockForced_forced_left_completion
import Theorems.Thm_ThreeSum_BlockEncoding_tuple_eq_of_output_leftSubset


set_option autoImplicit false
open ThreeSum ThreeSum.BlockForced
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding
namespace ThreeSum.BlockForced
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) :
    Set.InjOn (residual (h := h) I) (↑(completedTuples q I u) : Set (ChoiceTuple h J)) := by
  intro s hs t ht he
  apply tuple_eq_of_output_leftSubset
  · exact (Finset.mem_filter.mp hs).2.1.trans (Finset.mem_filter.mp ht).2.1.symm
  · rw [← forced_left_completion q I u s hs, ← forced_left_completion q I u t ht, he]
end ThreeSum.BlockForced
