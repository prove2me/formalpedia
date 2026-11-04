-- Prove2me | solution 1 for ThreeSum.Bands.overlap_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:14.261963+00:00
-- url     : https://prove2.me/submissions/d7f1d11b-2df1-417c-b0df-ad5f1d8e9a7a

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
import Theorems.Thm_ThreeSum_Bands_overlapOwner_injective

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution [Fintype I] [Fintype J]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) :
    Fintype.card {p : I × J // Overlap alo ahi blo bhi p} ≤
      Fintype.card I + Fintype.card J := by
  let f : {p : I × J // Overlap alo ahi blo bhi p} → I ⊕ J :=
    fun p => overlapOwner alo blo p.val
  have hinj : Function.Injective f := by
    intro p q h
    exact Subtype.ext (overlapOwner_injective hA hB p.property q.property h)
  simpa only [Fintype.card_sum] using Fintype.card_le_of_injective f hinj
end ThreeSum.Bands
