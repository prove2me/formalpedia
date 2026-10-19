-- Prove2me | solution 1 for RobustSpecClust.Round.frobSq_le_l1
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T10:15:03.356812+00:00
-- url     : https://prove2.me/submissions/08316fd6-0373-49e9-b88c-5b39e60db2c4

import Definitions.Def_RobustSpecClust_Round_Setting
import Mathlib.Tactic.Linarith

open RobustSpecClust.Round

/-- Appendix G, (G.6)(iii): bounded entry errors convert an entrywise
    absolute-error bound into a squared Frobenius-error bound. -/
theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hB : ∀ i j, 0 ≤ B i j ∧ B i j ≤ 1) :
    frobSq (A - B) ≤ l1 (A - B) := by
  unfold frobSq l1
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  change (A i j - B i j) ^ 2 ≤ |A i j - B i j|
  rcases hA i j with ⟨hA0, hA1⟩
  rcases hB i j with ⟨hB0, hB1⟩
  have hbound : |A i j - B i j| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hprod := mul_nonneg (abs_nonneg (A i j - B i j))
    (sub_nonneg.mpr hbound)
  nlinarith [sq_abs (A i j - B i j)]
