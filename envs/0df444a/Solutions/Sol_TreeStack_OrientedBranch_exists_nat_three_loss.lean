-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_nat_three_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:45.663437+00:00
-- url     : https://prove2.me/submissions/ed9e23e9-7171-4464-bc91-e30f685646a6

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
theorem _root_.solution {a b : ℤ}
    (hle : a ≤ b) (hmod : a % 3 = b % 3) :
    ∃ k : ℕ, a = b - 3 * (k : ℤ) := by
  have hme : a ≡ b [ZMOD 3] := by
    change a % 3 = b % 3
    exact hmod
  have hdvd : (3 : ℤ) ∣ b - a :=
    Int.modEq_iff_dvd.mp hme
  rcases hdvd with ⟨k, hk⟩
  have hk0 : 0 ≤ k := by
    omega
  refine ⟨k.toNat, ?_⟩
  rw [Int.toNat_of_nonneg hk0]
  omega
end TreeStack.OrientedBranch
