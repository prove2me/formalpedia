-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf.ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:25:24.897556+00:00
-- url     : https://prove2.me/submissions/06b0ed5a-9582-4e3b-b63d-3b1828828e98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountRhoPArithStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CountPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf
theorem _root_.solution (T c : ℕ) (hT : 0 < T) : ∀ k : ℕ,
    (1 - (k : ℝ) * c / T) * ((T + c + k).choose k : ℝ) ≤ ((T + k).choose k : ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hA : ((T + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + k + 1) * ((T + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + k) k
      rw [show T + (k + 1) = T + k + 1 by ring]
      have h' : ((T + k + 1) * (T + k).choose k : ℕ) = ((T + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hB : ((T + c + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + c + k + 1) * ((T + c + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + c + k) k
      rw [show T + c + (k + 1) = T + c + k + 1 by ring]
      have h' : ((T + c + k + 1) * (T + c + k).choose k : ℕ) = ((T + c + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hBn : (0 : ℝ) ≤ ((T + c + k).choose k : ℝ) := Nat.cast_nonneg _
    have hAn : (0 : ℝ) ≤ ((T + k).choose k : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    push_cast
    rw [← mul_le_mul_iff_of_pos_right hk1, mul_assoc, hB, hA]
    by_cases hs : 1 - ((k : ℝ) + 1) * c / T ≤ 0
    · have : (1 - ((k : ℝ) + 1) * c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hs (by positivity)
      have : (0 : ℝ) ≤ (T + k + 1) * ((T + k).choose k : ℝ) := by positivity
      linarith
    · push_neg at hs
      set u := 1 - (k : ℝ) * c / T with hu
      have hu1 : u ≤ 1 := by
        have : 0 ≤ (k : ℝ) * c / T := by positivity
        rw [hu]; linarith
      have hcT : (c : ℝ) / T * T = c := by field_simp
      have e1 : 1 - ((k : ℝ) + 1) * c / T = u - c / T := by rw [hu]; ring
      rw [e1]
      have step : (u - c / T) * (T + c + k + 1) ≤ u * (T + k + 1) := by
        have : (u - c / T) * (T + c + k + 1) = u * (T + k + 1) + (u * c - c / T * T - c / T * (c + k + 1)) := by ring
        rw [this, hcT]
        have h1 : u * c ≤ c := by nlinarith
        have h2 : 0 ≤ (c : ℝ) / T * (c + k + 1) := by positivity
        linarith
      have hupos : 0 ≤ u - c / T := by linarith
      calc (u - c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ))
          = ((u - c / T) * (T + c + k + 1)) * ((T + c + k).choose k : ℝ) := by ring
        _ ≤ (u * (T + k + 1)) * ((T + c + k).choose k : ℝ) := mul_le_mul_of_nonneg_right step hBn
        _ = (T + k + 1) * (u * ((T + c + k).choose k : ℝ)) := by ring
        _ ≤ (T + k + 1) * ((T + k).choose k : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)
end ReciprocityTheory.ChartRestriction.G.AR.Up.CountPf
