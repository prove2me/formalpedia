-- Prove2me | solution 1 for ThreeSum.SparseBoxes.IsInitial.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:11.67709+00:00
-- url     : https://prove2.me/submissions/c4a8ce06-92c3-4db5-b6ad-381d0e8a9c5a

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_SparseBoxes

set_option autoImplicit false
open ThreeSum ThreeSum.SparseBoxes
open scoped BigOperators
variable {α : Type*} [LinearOrder α]
namespace ThreeSum.SparseBoxes
namespace IsInitial
theorem _root_.solution {flags u v : Finset α}
    (hu : IsInitial flags u) (hv : IsInitial flags v) (hc : u.card = v.card) :
    u = v := by
  apply Finset.eq_of_subset_of_card_le
  · intro a hau
    by_contra hav
    have hex : ∃ b ∈ v, b ∉ u := by
      by_contra hn
      push Not at hn
      have he : v = u := Finset.eq_of_subset_of_card_le hn (by omega)
      exact hav (he.symm ▸ hau)
    obtain ⟨b, hbv, hbu⟩ := hex
    rcases lt_trichotomy a b with hab | hab | hba
    · exact hav (hv.2 b hbv a (hu.1 hau) hab)
    · subst b
      exact hbu hau
    · exact hbu (hu.2 a hau b (hv.1 hbv) hba)
  · omega
end IsInitial
end ThreeSum.SparseBoxes
