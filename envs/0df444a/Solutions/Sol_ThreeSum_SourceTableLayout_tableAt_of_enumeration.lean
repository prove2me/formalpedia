-- Prove2me | solution 1 for ThreeSum.SourceTableLayout.tableAt_of_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:11.881951+00:00
-- url     : https://prove2.me/submissions/c07ad570-6ba1-4347-af0d-9f6105889743

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Mathlib.Data.List.GetD
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Theorems.Thm_ThreeSum_SourceTableLayout_enumerateDownset_getD_subsetRank
import Theorems.Thm_ThreeSum_SubsetAddress_subsetRank_lt


set_option autoImplicit false
open ThreeSum ThreeSum.SourceTableLayout
open SubsetAddress
set_option maxHeartbeats 800000
namespace ThreeSum.SourceTableLayout
theorem _root_.solution {L cut base : ℕ} {μ : ℕ → ℤ}
    (value : ℕ → ℤ) (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < downsetCap L cut,
      μ (base+i) = value ((enumerateDownset L cut).getD i 0))
    (hvalue : ∀ S, S.card ≤ cut → value (subsetMask S) = f S) :
    LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (subsetRank_lt hS),enumerateDownset_getD_subsetRank S hS]
  exact hvalue S hS
end ThreeSum.SourceTableLayout
