-- Prove2me | solution 1 for ThreeSum.Bands.relevant_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:15.500115+00:00
-- url     : https://prove2.me/submissions/1ac41ace-e3f3-4800-8da0-1e8c1d29d171

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
import Theorems.Thm_ThreeSum_Bands_tripleOwner_injective

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution [Fintype I] [Fintype J] [Fintype K]
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi) :
    Fintype.card {p : I × (J × K) // Relevant alo ahi blo bhi clo chi p} ≤
      Fintype.card J * Fintype.card K +
        Fintype.card I * (Fintype.card J + Fintype.card K) := by
  let f : {p : I × (J × K) // Relevant alo ahi blo bhi clo chi p} →
      (J × K) ⊕ (I × (J ⊕ K)) := fun p => tripleOwner alo blo bhi clo p.val
  have hinj : Function.Injective f := by
    intro p q h
    exact Subtype.ext (tripleOwner_injective hA hB hC p.property q.property h)
  simpa only [Fintype.card_sum, Fintype.card_prod] using Fintype.card_le_of_injective f hinj
end ThreeSum.Bands
