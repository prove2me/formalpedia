-- Prove2me | solution 1 for StabilityDichotomies.Approximability.monotone_hamming_height
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:03:38.507256+00:00
-- url     : https://prove2.me/submissions/97967eb4-26d4-415d-ad9a-766bdfe02656

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V] (x y : V → Bool) (hxy : x ≤ y) :
    (hammingDist x y : ℝ) =
      (∑ v : V, if y v then (1 : ℝ) else 0) - ∑ v : V, if x v then (1 : ℝ) else 0 := by
  change (((Finset.univ.filter fun v => x v ≠ y v).card : ℕ) : ℝ) = _
  rw [← Finset.sum_boole (fun v => x v ≠ y v) Finset.univ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have h := hxy v
  cases hx : x v <;> cases hy : y v <;> simp_all
  exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
