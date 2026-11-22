-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_layer_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:25.909456+00:00
-- url     : https://prove2.me/submissions/95751f0c-4f5b-4721-9125-f1056c90cf3a

import Definitions.Def_Paper_Formalized
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_Paper_RoundingEstimates

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (a ℓ : ℕ → ℝ) (N : ℕ) {b K : ℝ}
    (hseed : b ≤ a 0) (hbudget : K < 2 ^ N * b) (hupper : a N ≤ K)
    (hadd : ∀ i < N, a i + ℓ i ≤ a (i + 1)) :
    ∃ i < N, ℓ i ≤ a i := by
  by_contra hn
  have hbad : ∀ i < N, a i < ℓ i := by
    intro i hi
    exact lt_of_not_ge fun h => hn ⟨i, hi, h⟩
  have hg : ∀ i ≤ N, 2 ^ i * b ≤ a i := by
    intro i hi
    induction i with
    | zero => simpa using hseed
    | succ i ih =>
      have hprev := ih (by omega)
      have hstep := hadd i (by omega)
      have hstrict := hbad i (by omega)
      rw [pow_succ]
      nlinarith
  have := hg N le_rfl
  linarith
end Paper.Hypergraph
