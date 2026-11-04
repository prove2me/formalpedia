-- Prove2me | solution 1 for ThreeSum.BlockSourceTableLayout.right_tableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:46.052666+00:00
-- url     : https://prove2.me/submissions/0ceb59b0-125c-46cd-8228-29d09016d67a

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
    (P shift : ℤ) (C : Finset β) (c : β → ℤ) (q : GlobalOutput h J)
    (hread : ∀ i < downsetCap (J*(512*h)) cut,
      μ (base+i) = (rightWeights (outputOccurrences q) P shift C c (sets h J cut i) : ℤ)) :
    LightZetaCell.TableAt μ base cut (BlockIndexedQuery.rightSource P shift C c q) := by
  apply SourceTableLayout.tableAt_of_setAt
  exact hread
end ThreeSum.BlockSourceTableLayout
