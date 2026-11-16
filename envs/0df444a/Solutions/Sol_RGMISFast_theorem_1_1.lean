-- Prove2me | solution 1 for RGMISFast.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T00:48:32.205203+00:00
-- url     : https://prove2.me/submissions/e01cf0d1-36ee-45a0-8236-16d54dcc7b37

import Theorems.Thm_RGMISFast_observation_2_2
import Theorems.Thm_RGMISFast_proposition_4_2
import Theorems.Thm_RGMISFast_eq_12
import Theorems.Thm_RGMISFast_query_measurable_rank_regular
import Theorems.Thm_RGMISFast_lintegral_le_two_scale_of_exp_tail
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false
theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ),
      2 ≤ Δ → (∀ v, G.degree v ≤ Δ) → ∀ u : V,
        Measurable (fun r : V → ℝ => Q G u r) ∧
        (∀ h : ℝ, 0 ≤ h →
          rankLaw V {r | C * (Δ : ℝ) ^ 90 * (1 + h) < (Q G u r : ℝ)} ≤
            ENNReal.ofReal (Real.exp (-h))) ∧
        ∫⁻ r, (Q G u r : ℝ≥0∞) ∂(rankLaw V) ≤ ENNReal.ofReal (2 * C * (Δ : ℝ) ^ 90) := by
  classical
  obtain ⟨C, hC, htree⟩ := proposition_4_2
  refine ⟨C, hC, ?_⟩
  intro V _ _ G _ Δ hΔ hdeg u
  obtain ⟨hm, hreg⟩ := query_measurable_rank_regular G u
  have ht : ∀ h : ℝ, 0 ≤ h →
      rankLaw V {r | C * (Δ : ℝ)^90 * (1+h) < (Q G u r : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-h)) := by
    intro h hh
    have hsub : ∀ᵐ r ∂(rankLaw V),
        r ∈ {r | C * (Δ : ℝ)^90 * (1+h) < (Q G u r : ℝ)} →
        r ∈ {r | ¬ GoodEvent G Δ u (h+8) r} := by
      filter_upwards [hreg] with r hr
      intro hbig hgood
      obtain ⟨_, _, _, _, _, hnodup, hlen, T, hnodes, _⟩ :=
        observation_2_2 G u r hr.1 hr.2
      have hcard : T.nodes.card = Q G u r := by
        rw [hnodes, List.toFinset_card_of_nodup hnodup, hlen]
      have hb := htree V G Δ hΔ hdeg u h hh r hr.1 hr.2 hgood T
      rw [hcard] at hb
      exact (not_lt_of_ge hb) hbig
    obtain ⟨hprob, hnum⟩ := eq_12 G Δ hΔ hdeg u h hh
    exact (measure_mono_ae hsub).trans (hprob.trans (ENNReal.ofReal_le_ofReal hnum.le))
  refine ⟨hm, ht, ?_⟩
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (rankLaw V) := by unfold rankLaw; infer_instance
  have he := lintegral_le_two_scale_of_exp_tail (rankLaw V) (fun r => Q G u r)
    hm (C * (Δ : ℝ)^90) (mul_pos hC (pow_pos hΔpos _)) ht
  simpa only [mul_assoc] using he
