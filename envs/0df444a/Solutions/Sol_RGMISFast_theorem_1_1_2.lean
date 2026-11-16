-- Prove2me | solution 2 for RGMISFast.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T01:29:39.076304+00:00
-- url     : https://prove2.me/submissions/babcdebe-78c0-4153-98c9-7fd2351d0456

import Theorems.Thm_RGMISFast_observation_2_2
import Theorems.Thm_RGMISFast_proposition_4_2
import Theorems.Thm_RGMISFast_lemma_3_1
import Theorems.Thm_RGMISFast_lemma_3_2
import Theorems.Thm_RGMISFast_lemma_A_1
import Theorems.Thm_RGMISFast_query_measurable_rank_regular
import Theorems.Thm_RGMISFast_lintegral_le_two_scale_of_exp_tail
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false
namespace MainGoodEvent
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

/-- The union bound and strict numerical estimate, with the three probability
bounds exposed as hypotheses rather than imported open theorems. -/
theorem eq12_of_probability_bounds {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (u : V) (h : ℝ)
    (ha : rankLaw V {r | ¬ (EntryEvent G Δ u (h+8) r ∧ GrowthEvent G Δ u (h+8) r)} ≤
      ENNReal.ofReal (320*Real.exp (-(h+8))))
    (hb : rankLaw V {r | ¬ TopEvent G u (h+8) r} ≤ ENNReal.ofReal (Real.exp (-(h+8))))
    (hc : rankLaw V {r | ¬ LowRankEvent G Δ u (h+8) r} ≤ ENNReal.ofReal (Real.exp (-(h+8))/4)) :
    rankLaw V {r | ¬ GoodEvent G Δ u (h+8) r} ≤
      ENNReal.ofReal ((320+1+1/4)*Real.exp (-(h+8))) ∧
      (320+1+1/4)*Real.exp (-(h+8)) < Real.exp (-h) := by
  constructor
  · have hs : {r | ¬ GoodEvent G Δ u (h+8) r} =
        ({r | ¬ (EntryEvent G Δ u (h+8) r ∧ GrowthEvent G Δ u (h+8) r)} ∪
         {r | ¬ TopEvent G u (h+8) r}) ∪ {r | ¬ LowRankEvent G Δ u (h+8) r} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_union, GoodEvent]
      tauto
    rw [hs]
    calc
      _ ≤ (rankLaw V {r | ¬ (EntryEvent G Δ u (h+8) r ∧ GrowthEvent G Δ u (h+8) r)} +
          rankLaw V {r | ¬ TopEvent G u (h+8) r}) +
          rankLaw V {r | ¬ LowRankEvent G Δ u (h+8) r} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ (ENNReal.ofReal (320 * Real.exp (-(h+8))) + ENNReal.ofReal (Real.exp (-(h+8)))) +
          ENNReal.ofReal (Real.exp (-(h+8)) / 4) := add_le_add (add_le_add ha hb) hc
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  · have he : (320 + 1 + 1 / 4 : ℝ) < Real.exp 8 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 8) 6
      norm_num [Finset.sum_range_succ] at h
      linarith
    have hp := mul_lt_mul_of_pos_right he (Real.exp_pos (-(h+8)))
    have hid : Real.exp 8 * Real.exp (-(h+8)) = Real.exp (-h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [hid] at hp
end MainGoodEvent

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
    have hL : 8 ≤ h+8 := by linarith
    obtain ⟨hprob, hnum⟩ := MainGoodEvent.eq12_of_probability_bounds G Δ u h
      (lemma_3_1 G Δ hΔ hdeg u (h+8) hL)
      (lemma_3_2 G u (h+8)).1
      (lemma_A_1 G Δ hΔ hdeg u (h+8) hL)
    exact (measure_mono_ae hsub).trans (hprob.trans (ENNReal.ofReal_le_ofReal hnum.le))
  refine ⟨hm, ht, ?_⟩
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (rankLaw V) := by unfold rankLaw; infer_instance
  have he := lintegral_le_two_scale_of_exp_tail (rankLaw V) (fun r => Q G u r)
    hm (C * (Δ : ℝ)^90) (mul_pos hC (pow_pos hΔpos _)) ht
  simpa only [mul_assoc] using he
