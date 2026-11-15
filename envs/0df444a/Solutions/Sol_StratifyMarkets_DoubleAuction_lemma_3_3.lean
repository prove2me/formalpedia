-- Prove2me | solution 1 for StratifyMarkets.DoubleAuction.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T06:36:31.530354+00:00
-- url     : https://prove2.me/submissions/ec942ace-6f1e-45b3-807e-079e7c6348d1

import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
import Mathlib

set_option autoImplicit false

-- Solutions.Sol_StratifyMarkets_DoubleAuction_lemma_3_3
section
open MeasureTheory Set StratifyMarkets.DoubleAuction

theorem solution (I : BTInstance) (c c' : ℝ) (hc : 0 ≤ c) (hcc' : c < c') (hc' : c' ≤ 1)
    (sc sc' : ℝ) (hsc : sc ∈ Icc (0 : ℝ) 1)
    (hsc_max : IsMaxOn (fun s => (s - c) * I.Fbar s) (Icc 0 1) sc)
    (hsc' : sc' ∈ Icc (0 : ℝ) 1)
    (hsc'_max : IsMaxOn (fun s => (s - c') * I.Fbar s) (Icc 0 1) sc')
    (hF : 0 < I.Fbar c) : sc ≤ sc' := by
  let := I.isProb_B
  let := I.noAtoms_B
  have hint : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici 0) I.μB :=
    (integrable_const 1).integrableOn
  have hcont : ContinuousOn I.Fbar (Ici 0) := by
    change ContinuousOn (fun b => (I.μB (Ici b)).toReal) (Ici 0)
    simpa only [setIntegral_one_eq_measureReal, measureReal_def] using hint.continuousOn_Ici_primitive_Ici
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp (hcont c hc)) (I.Fbar c) hF
  let u := min ((1 - c) / 2) (δ / 2)
  have hu : 0 < u := lt_min (by linarith) (by linarith)
  have hu₁ : c + u ≤ 1 := by linarith [min_le_left ((1-c)/2) (δ/2)]
  have hdist : dist (c + u) c < δ := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hu]
    linarith [min_le_right ((1-c)/2) (δ/2)]
  have hclose := hnear (show c + u ∈ Ici 0 by exact add_nonneg hc hu.le) hdist
  rw [Real.dist_eq, abs_lt] at hclose
  have htrial : 0 < ((c + u) - c) * I.Fbar (c + u) := mul_pos (by linarith) (by linarith [hclose.1])
  have hprofit := htrial.trans_le (isMaxOn_iff.mp hsc_max _ ⟨add_nonneg hc hu.le, hu₁⟩)
  have htail : 0 < I.Fbar sc := lt_of_le_of_ne ENNReal.toReal_nonneg (by
    intro hz
    change 0 = I.Fbar sc at hz
    simp [← hz] at hprofit)
  have h₁ := isMaxOn_iff.mp hsc_max sc' hsc'
  have h₂ := isMaxOn_iff.mp hsc'_max sc hsc
  have hrevealed : 0 ≤ (c' - c) * (I.Fbar sc - I.Fbar sc') := by linarith only [h₁, h₂]
  by_contra! hrev
  have hanti : I.Fbar sc ≤ I.Fbar sc' := measureReal_mono (Ici_subset_Ici.mpr hrev.le)
  have heq : I.Fbar sc' = I.Fbar sc := le_antisymm
    (sub_nonneg.mp (nonneg_of_mul_nonneg_right hrevealed (sub_pos.mpr hcc'))) hanti
  rw [heq] at h₂
  exact (not_le_of_gt (mul_lt_mul_of_pos_right (sub_lt_sub_right hrev _) htail)) h₂
end
