-- Prove2me | solution 1 for OWMR.slValue_setup_scale
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T01:17:48.296355+00:00
-- url     : https://prove2.me/submissions/145d8e5a-4f47-46d4-a812-babc6abcdc6f

import Definitions.Def_owmr_single_location
import Mathlib.Order.Filter.ENNReal

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ)
    (hf : ∀ y, 0 ≤ f y) (K : ℝ) {a : ℝ} (ha : 1 ≤ a) :
    slValue ρ f (a * K) ≤ ENNReal.ofReal a * slValue ρ f K := by
  have ha0 : ENNReal.ofReal a ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hatop : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold slValue
  simp only [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_mono fun U => iInf_mono fun _ => iInf_mono fun ν => iInf_mono fun _ =>
    iInf_mono fun q => iInf_mono fun _ => ?_
  unfold slAvgCost
  rw [← ENNReal.limsup_const_mul_of_ne_top hatop]
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun T => ?_)
  dsimp only
  rw [mul_left_comm, ← lintegral_const_mul' _ _ hatop]
  gcongr with ω
  rw [Finset.mul_sum]
  gcongr with t ht
  rw [← ENNReal.ofReal_mul (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have hfx := hf (slPos 0 q ω.1 (padHist T ω.2) t)
  unfold slPeriodCost
  split_ifs <;> nlinarith
