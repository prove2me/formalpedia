-- Prove2me | solution 1 for Paper.Hypergraph.cutoff_layer_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:01:33.554788+00:00
-- url     : https://prove2.me/submissions/f06e9b2f-30c3-4649-84c5-b95af2f99d00

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
theorem _root_.solution {r K : ℝ} (hr : 0 < r) (hK : r / 2 ≤ K) :
    let L := Real.logb 2 (K / r)
    let δ := r / (9 + 2 * L)
    ∃ N : ℕ, 0 < N ∧
      r / 4 + (N : ℝ) * (3 * δ / 2) ≤ r ∧
      K < (2 : ℝ) ^ N * (5 * r / 56) ∧
      ∀ q : ℝ, q < δ / 2 → 5 * r / 56 ≤ (r / 4 - q) / 2 := by
  dsimp
  let L := Real.logb 2 (K / r)
  have ht : 0 < K / r := div_pos (by linarith) hr
  have hL : -1 ≤ L := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) ht).2
    norm_num
    exact (le_div_iff₀ hr).2 (by linarith)
  have hD : 0 < 9 + 2 * L := by linarith
  let N : ℕ := ⌊L + 7 / 2⌋₊ + 1
  have hNlo : L + 7 / 2 < (N : ℝ) := by
    simpa [N] using Nat.lt_floor_add_one (L + 7 / 2)
  have hNhi : (N : ℝ) ≤ L + 9 / 2 := by
    have hf := Nat.floor_le (show 0 ≤ L + 7 / 2 by linarith)
    dsimp [N]
    push_cast
    linarith
  have hpowconst : (56 / 5 : ℝ) < (2 : ℝ) ^ (7 / 2 : ℝ) := by
    have hs : ((2 : ℝ) ^ (7 / 2 : ℝ)) ^ (2 : ℕ) = 128 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hn := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (7 / 2 : ℝ)
    nlinarith
  have hgrowth : (K / r) * (56 / 5) < (2 : ℝ) ^ N := by
    calc
      _ < (K / r) * (2 : ℝ) ^ (7 / 2 : ℝ) := mul_lt_mul_of_pos_left hpowconst ht
      _ = (2 : ℝ) ^ (L + 7 / 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show (2 : ℝ) ^ L = K / r from
          Real.rpow_logb (by norm_num) (by norm_num) ht]
      _ < (2 : ℝ) ^ N := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hNlo
  refine ⟨N, by dsimp [N]; omega, ?_, ?_, ?_⟩
  · change r / 4 + (N : ℝ) * (3 * (r / (9 + 2 * L)) / 2) ≤ r
    apply (le_of_mul_le_mul_right ?_ hD)
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hNhi hr.le]
  · have hg := mul_lt_mul_of_pos_right hgrowth hr
    field_simp at hg
    nlinarith
  · intro q hq
    change q < (r / (9 + 2 * L)) / 2 at hq
    have hδ : r / (9 + 2 * L) ≤ r / 7 := by
      apply div_le_div_of_nonneg_left hr.le (by norm_num)
      linarith
    linarith
end Paper.Hypergraph
