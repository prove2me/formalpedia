-- Prove2me | solution 1 for ThreeSum.BlockSourceTableLayout.left_tableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:44.756205+00:00
-- url     : https://prove2.me/submissions/d9daec46-b2c6-40a1-91cc-9cdc95819a20

import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_BlockIndexedQuery
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_tableAt_of_setAt


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceTableLayout
open SubsetAddress BlockIndex BlockEncoding BlockRows GlobalEncoding
namespace ThreeSum.BlockSourceTableLayout
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J cut base : ℕ} {μ : ℕ → ℤ}
    (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (leftWeights (outputOccurrences q) P B b (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.leftSource P B b q) := by
  apply SourceTableLayout.tableAt_of_setAt
  exact hread
end ThreeSum.BlockSourceTableLayout
