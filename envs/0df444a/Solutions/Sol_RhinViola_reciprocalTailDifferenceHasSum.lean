-- Prove2me | solution 1 for RhinViola.reciprocalTailDifferenceHasSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:38:04.002091+00:00
-- url     : https://prove2.me/submissions/ed6469b8-66cd-4c47-9821-54385ac3dfba

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

open Filter

theorem solution (a : ℕ) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (((k + a + 1 : ℕ) : ℝ)) -
        (1 : ℝ) / (((k + a + 2 : ℕ) : ℝ)))
      ((1 : ℝ) / (((a + 1 : ℕ) : ℝ))) := by
  let f : ℕ → ℝ := fun k =>
    (1 : ℝ) / (((k + a + 1 : ℕ) : ℝ)) -
      (1 : ℝ) / (((k + a + 2 : ℕ) : ℝ))
  have hpartial : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, f k =
        (1 : ℝ) / (((a + 1 : ℕ) : ℝ)) -
          (1 : ℝ) / (((n + a + 1 : ℕ) : ℝ)) := by
    intro n
    induction n with
    | zero =>
        simp [f]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [f]
        push_cast
        ring
  have hnonneg : ∀ k : ℕ, 0 ≤ f k := by
    intro k
    have hx : 0 < (((k + a + 1 : ℕ) : ℝ)) := by positivity
    have hy : 0 < (((k + a + 2 : ℕ) : ℝ)) := by positivity
    have hid :
        f k =
          (1 : ℝ) /
            ((((k + a + 1 : ℕ) : ℝ)) * (((k + a + 2 : ℕ) : ℝ))) := by
      simp only [f]
      field_simp [ne_of_gt hx, ne_of_gt hy]
      push_cast
      ring
    rw [hid]
    positivity
  have hden :
      Tendsto (fun n : ℕ => (((n + a + 1 : ℕ) : ℝ))) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => n + (a + 1)) atTop atTop :=
      Filter.tendsto_add_atTop_nat (a + 1)
    have hcast :
        Tendsto ((↑) : ℕ → ℝ) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, Nat.add_assoc] using hcast.comp hnat
  have htail :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((n + a + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp hden
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  simpa [hpartial] using
    (tendsto_const_nhds.sub htail :
      Tendsto
        (fun n : ℕ =>
          (1 : ℝ) / (((a + 1 : ℕ) : ℝ)) -
            (1 : ℝ) / (((n + a + 1 : ℕ) : ℝ)))
        atTop
        (nhds ((1 : ℝ) / (((a + 1 : ℕ) : ℝ)) - 0)))
