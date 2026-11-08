-- Prove2me | solution 1 for ProcessingNetworks.PathCompact.lemma_A_10_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:21:50.06424+00:00
-- url     : https://prove2.me/submissions/2f5e5609-9686-43e6-afd9-cfca08e95492

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL
import Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC

open Filter Topology
open scoped NNReal

open ProcessingNetworks.PathCompact in
theorem solution (fs : ℕ → ℝ≥0 → ℝ) (hD : ∀ n, RBMSensitivity.IsRCLL (fs n))
    (hmono : ∀ n, Monotone (fs n)) (f : ℝ≥0 → ℝ) (hf : Continuous f)
    (hrat : ∀ t : ℝ≥0, (∃ q : ℚ, (q : ℝ) = (t : ℝ)) →
      Tendsto (fun n => fs n t) atTop (𝓝 (f t))) :
    ∀ t : ℝ≥0, Tendsto (fun n => fs n t) atTop (𝓝 (f t)) := by
  intro t
  rw [tendsto_order]
  constructor
  · intro a ha
    have hev : ∀ᶠ s in 𝓝 t, a < f s := hf.continuousAt.eventually (lt_mem_nhds ha)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have key : ∃ s : ℝ≥0, s ≤ t ∧ a < f s ∧ ∃ q : ℚ, (q : ℝ) = (s : ℝ) := by
      rcases eq_or_lt_of_le (show (0:ℝ≥0) ≤ t from t.2) with h0 | h0
      · exact ⟨t, le_rfl, ha, ⟨0, by rw [← h0]; simp⟩⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (show (0:ℝ) < t from h0)
          (show (t:ℝ) - δ < t by linarith))
        have hq0 : (0:ℝ) ≤ q := le_trans (le_max_left _ _) hq1.le
        set s : ℝ≥0 := ⟨q, hq0⟩ with hs
        have hsq : (s : ℝ) = q := rfl
        refine ⟨s, ?_, hball ?_, ⟨q, hsq.symm⟩⟩
        · show (s : ℝ) ≤ t
          rw [hsq]; exact hq2.le
        · rw [NNReal.dist_eq, hsq]
          rw [abs_lt]
          constructor
          · linarith [le_max_right (0:ℝ) ((t:ℝ) - δ)]
          · linarith
    obtain ⟨s, hst, has, hsq⟩ := key
    have := (tendsto_order.1 (hrat s hsq)).1 a has
    filter_upwards [this] with n hn
    exact lt_of_lt_of_le hn (hmono n hst)
  · intro a ha
    have hev : ∀ᶠ s in 𝓝 t, f s < a := hf.continuousAt.eventually (gt_mem_nhds ha)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t:ℝ) < t + δ by linarith)
    have hq0 : (0:ℝ) ≤ q := le_trans t.2 hq1.le
    set s : ℝ≥0 := ⟨q, hq0⟩ with hs
    have hsq : (s : ℝ) = q := rfl
    have hst : t ≤ s := by
      show (t:ℝ) ≤ s
      rw [hsq]; exact hq1.le
    have has : f s < a := by
      apply hball
      rw [NNReal.dist_eq, hsq]
      rw [abs_lt]
      constructor <;> linarith
    have := (tendsto_order.1 (hrat s ⟨q, hsq.symm⟩)).2 a has
    filter_upwards [this] with n hn
    exact lt_of_le_of_lt (hmono n hst) hn
