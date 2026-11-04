-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.rightSource_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:25.581653+00:00
-- url     : https://prove2.me/submissions/a23bdea7-75d7-42f1-bc3c-1d4b4483cff3

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightWeights_le_card

set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |rightSource P d C c q S| ≤ C.card := by
  unfold rightSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast rightWeights_le_card (outputOccurrences q) P d C c _
end ThreeSum.BlockIndexedQuery
