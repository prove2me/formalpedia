-- Prove2me | solution 1 for ThreeSum.SparseBoxes.IsLargest.unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:55.348526+00:00
-- url     : https://prove2.me/submissions/6722741c-d7e0-45d1-b335-8b71ead926a1

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
namespace IsLargest
theorem _root_.solution {t : ℕ} {m u v : Finset α}
    (hu : IsLargest t m u) (hv : IsLargest t m v) : u = v := by
  obtain ⟨hum, huc, huo⟩ := hu
  obtain ⟨hvm, hvc, hvo⟩ := hv
  apply Finset.eq_of_subset_of_card_le
  · intro a hau
    by_contra hav
    have hex : ∃ b ∈ v, b ∉ u := by
      by_contra hn
      push Not at hn
      have he : v = u := Finset.eq_of_subset_of_card_le hn (by omega)
      exact hav (he.symm ▸ hau)
    obtain ⟨b, hbv, hbu⟩ := hex
    exact (lt_asymm (huo a hau b (hvm hbv) hbu)) (hvo b hbv a (hum hau) hav)
  · omega
end IsLargest
end ThreeSum.SparseBoxes
