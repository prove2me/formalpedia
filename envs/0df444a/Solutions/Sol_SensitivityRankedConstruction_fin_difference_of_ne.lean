-- Prove2me | solution 1 for SensitivityRankedConstruction.fin_difference_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:22:36.434908+00:00
-- url     : https://prove2.me/submissions/275075f2-9ac9-4b83-a579-efe04188d1c3

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Pairwise orientation gives the guard that separates strict row colors. -/
open SensitivityRankedConstruction
open SensitivityHighHeadGuardBridge


theorem _root_.solution {n : ℕ} (x y : Fin n) (hne : x ≠ y) :
    0 < (y.val + n - x.val) % n ∧ (y.val + n - x.val) % n < n ∧
      (x.val + n - y.val) % n = n - (y.val + n - x.val) % n := by
  have hx := x.isLt
  have hy := y.isLt
  have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
  have key : ∀ a b : ℕ, a < n → b < n → a < b → (b + n - a) % n = b - a ∧ (a + n - b) % n = a + n - b := by
    intro a b ha hb hab
    refine ⟨?_, Nat.mod_eq_of_lt (by omega)⟩
    rw [show b + n - a = (b - a) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rcases lt_or_gt_of_ne hne' with h | h
  · obtain ⟨h1, h2⟩ := key _ _ hx hy h
    rw [h1, h2]; omega
  · obtain ⟨h1, h2⟩ := key _ _ hy hx h
    rw [h1, h2]; omega


