-- Prove2me | solution 1 for ThreeSum.Bands.tripleOwner_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:31:32.008076+00:00
-- url     : https://prove2.me/submissions/9e66eff6-3818-43a4-8e72-3801427d1bef

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Bands
import Theorems.Thm_ThreeSum_Bands_interval_unique
import Theorems.Thm_ThreeSum_Bands_separated_shift
import Theorems.Thm_ThreeSum_Bands_overlapOwner_injective

set_option autoImplicit false
open ThreeSum ThreeSum.Bands
variable {I J K : Type*}
namespace ThreeSum.Bands
theorem _root_.solution
    {alo ahi : I → ℤ} {blo bhi : J → ℤ} {clo chi : K → ℤ}
    (hA : Separated alo ahi) (hB : Separated blo bhi) (hC : Separated clo chi)
    {p q : I × (J × K)} (hp : Relevant alo ahi blo bhi clo chi p)
    (hq : Relevant alo ahi blo bhi clo chi q)
    (heq : tripleOwner alo blo bhi clo p = tripleOwner alo blo bhi clo q) : p = q := by
  rcases p with ⟨i, j, k⟩
  rcases q with ⟨i', j', k'⟩
  change alo i ≤ chi k - blo j ∧ clo k - bhi j ≤ ahi i at hp
  change alo i' ≤ chi k' - blo j' ∧ clo k' - bhi j' ≤ ahi i' at hq
  unfold tripleOwner at heq
  dsimp only at heq
  by_cases h : alo i < clo k - bhi j
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp only [if_pos h, if_pos h'] at heq
      have hjk : (j, k) = (j', k') := Sum.inl.inj heq
      have hj := congrArg Prod.fst hjk
      have hk := congrArg Prod.snd hjk
      dsimp only at hj hk
      subst j'
      subst k'
      have hi : i = i' := interval_unique hA (by omega) hp.2 (by omega) hq.2
      subst i'
      rfl
    · simp [h, h'] at heq
  · by_cases h' : alo i' < clo k' - bhi j'
    · simp [h, h'] at heq
    · simp only [if_neg h, if_neg h'] at heq
      have he := Sum.inr.inj heq
      have hi := congrArg Prod.fst he
      dsimp only at hi
      subst i'
      have ho := congrArg Prod.snd he
      dsimp only at ho
      have hOverlap : Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j, k) := by
        constructor <;> dsimp only <;> omega
      have hOverlap' : Overlap (fun j => alo i + blo j) (fun j => alo i + bhi j) clo chi (j', k') := by
        constructor <;> dsimp only <;> omega
      have hjk := overlapOwner_injective (separated_shift hB (alo i)) hC hOverlap hOverlap' ho
      cases hjk
      rfl
end ThreeSum.Bands
