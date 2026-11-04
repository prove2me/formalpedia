-- Prove2me | solution 1 for ThreeSum.BlockIndexedQuery.leftSource_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:37.129587+00:00
-- url     : https://prove2.me/submissions/d535e99b-f23f-41ee-b43f-eb8b38c9529c

import Definitions.Def_Submission_ThreeSum_BlockIndex
import Definitions.Def_Submission_ThreeSum_StoredReporting
import Definitions.Def_Submission_ThreeSum_SubsetTransport
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Mathlib.Data.Fintype.Fin
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftWeights_le_card

set_option autoImplicit false
open ThreeSum ThreeSum.BlockIndexedQuery
open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.BlockIndexedQuery
theorem _root_.solution {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |leftSource P B b q S| ≤ B.card := by
  unfold leftSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast leftWeights_le_card (outputOccurrences q) P B b _
end ThreeSum.BlockIndexedQuery
