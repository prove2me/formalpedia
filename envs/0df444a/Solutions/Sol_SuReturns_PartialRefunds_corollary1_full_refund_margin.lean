-- Prove2me | solution 1 for SuReturns.PartialRefunds.corollary1_full_refund_margin
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:11:39.60821+00:00
-- url     : https://prove2.me/submissions/7b83ddc8-6a8b-4302-bc4a-73afb06ab13e

import Mathlib
import Definitions.Def_SuReturns_PartialRefunds_Model

open MeasureTheory ProbabilityTheory

open SuReturns.PartialRefunds

theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun v => v) ν) (s : ℝ) :
    ∀ p, (p - s) * keepProb ν p ≤ reservationPrice ν s - s := by
  intro p
  have hi : Integrable ((Set.Ici p).indicator (fun _ : ℝ => p - s)) ν :=
    (integrable_const (p-s)).indicator measurableSet_Ici
  have hm0 : Integrable (fun v : ℝ => max v s) ν := by
    have he : ((fun v : ℝ => v) ⊔ (fun _ => s)) = (fun v => max v s) := by
      funext v
      exact le_antisymm (sup_le (le_max_left v s) (le_max_right v s))
        (max_le le_sup_left le_sup_right)
    rw [← he]
    exact hν.sup (integrable_const s)
  have hm : Integrable (fun v : ℝ => max v s - s) ν :=
    hm0.sub (integrable_const s)
  have hle : ∫ v, (Set.Ici p).indicator (fun _ : ℝ => p-s) v ∂ν ≤
      ∫ v, (max v s - s) ∂ν := by
    apply integral_mono hi hm
    intro v
    by_cases hv : v ∈ Set.Ici p
    · simp only [Set.indicator_of_mem hv]
      exact sub_le_sub_right (le_trans hv (le_max_left v s)) s
    · simp only [Set.indicator_of_notMem hv]
      exact sub_nonneg.mpr (le_max_right v s)
  rw [integral_sub hm0 (integrable_const s)] at hle
  simpa [integral_indicator measurableSet_Ici, integral_const, keepProb,
    reservationPrice, measureReal_def, mul_comm] using hle




#print axioms solution
