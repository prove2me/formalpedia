-- Prove2me | solution 1 for SpatialDemandEq.Optimal.rate_gap_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:35:36.304955+00:00
-- url     : https://prove2.me/submissions/b02c3ca8-2e53-4735-86fe-7d5d8cd7ff04

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

open MeasureTheory
open SpatialDemandEq.Optimal

theorem solution {K : ℕ} (lam B : ℝ) (hB : lam < B) (a : Fin K → ℝ)
    (ha : ∀ k, 0 < a k) (k : Fin K) :
    1 / (optRates lam B a k - lam * a k) =
      1 / (B - lam) * (∑ j, Real.sqrt (a j)) * (1 / Real.sqrt (a k)) := by
  have hsk : 0 < Real.sqrt (a k) := Real.sqrt_pos.mpr (ha k)
  have hS : 0 < ∑ j, Real.sqrt (a j) :=
    Finset.sum_pos (fun j _ => Real.sqrt_pos.mpr (ha j)) ⟨k, Finset.mem_univ _⟩
  have hBl : 0 < B - lam := sub_pos.mpr hB
  unfold optRates
  rw [add_sub_cancel_left]
  field_simp
