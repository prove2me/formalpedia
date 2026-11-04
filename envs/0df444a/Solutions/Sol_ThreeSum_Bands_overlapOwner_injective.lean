-- Prove2me | solution 1 for ThreeSum.Bands.overlapOwner_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:07.73427+00:00
-- url     : https://prove2.me/submissions/73560e3b-7542-4ea3-ba78-b57515e4d5bc

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
import Theorems.Thm_ThreeSum_Bands_interval_unique

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution {alo ahi : I → ℤ} {blo bhi : J → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi)
    {p q : I × J} (hp : Overlap alo ahi blo bhi p) (hq : Overlap alo ahi blo bhi q)
    (heq : overlapOwner alo blo p = overlapOwner alo blo q) : p = q := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  unfold overlapOwner at heq
  dsimp only at heq
  change alo i ≤ bhi j ∧ blo j ≤ ahi i at hp
  change alo k ≤ bhi l ∧ blo l ≤ ahi k at hq
  by_cases h : alo i ≤ blo j
  · by_cases h' : alo k ≤ blo l
    · simp only [if_pos h, if_pos h'] at heq
      have hj : j = l := Sum.inr.inj heq
      subst l
      have hi : i = k := interval_unique hA h hp.2 h' hq.2
      subst k
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo k ≤ blo l
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have hi : i = k := Sum.inl.inj heq
      subst k
      have hj : j = l := interval_unique hB (by omega) hp.1 (by omega) hq.1
      subst l
      rfl
end ThreeSum.Bands
