-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.tableAt_of_setAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:24.045621+00:00
-- url     : https://prove2.me/submissions/10515ef6-7b6b-482a-afb2-2c53443f8747

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_setAt_subsetRank
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut base : ℕ} {μ : ℕ → ℤ}
    (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut, μ (base+i) = f (setAt L cut i)) :
    LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (subsetRank_lt hS),setAt_subsetRank S hS]
end ThreeSum.SourceTableLayout
