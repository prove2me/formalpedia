-- Prove2me | solution 1 for TsayQF.NoCommit.nc_production
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:01:51.060468+00:00
-- url     : https://prove2.me/submissions/7cff1e0f-e5a9-448c-aeb3-b0977efd849f

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQFNVAux
open Set Filter Topology

lemma min_inc_lower (x Q Q' : ℝ) (h : Q ≤ Q') :
    (Ioi Q').indicator (fun _ => Q' - Q) x ≤ min x Q' - min x Q := by
  by_cases hx : x ∈ Ioi Q'
  · rw [indicator_of_mem hx]
    have : Q' < x := hx
    rw [min_eq_right this.le, min_eq_right (by linarith)]
  · rw [indicator_of_notMem hx]
    have := min_le_min_left x h
    linarith

lemma min_inc_upper (x Q Q' : ℝ) (h : Q ≤ Q') :
    min x Q' - min x Q ≤ (Ioi Q).indicator (fun _ => Q' - Q) x := by
  by_cases hx : x ∈ Ioi Q
  · rw [indicator_of_mem hx]
    have : Q < x := hx
    rw [min_eq_right this.le]
    have := min_le_right x Q'
    linarith
  · rw [indicator_of_notMem hx]
    have : x ≤ Q := not_lt.1 hx
    rw [min_eq_left this, min_eq_left (by linarith)]
    simp

lemma real_Ioi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (x : ℝ) :
    ρ.real (Ioi x) = 1 - cdf ρ x := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

lemma int_min (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q : ℝ) :
    Integrable (fun y => min y Q) ρ := by
  have := hint.inf (integrable_const Q)
  exact this

lemma inc_lo (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q Q' : ℝ)
    (h : Q ≤ Q') :
    (Q' - Q) * (1 - cdf ρ Q') ≤ ∫ y, min y Q' ∂ρ - ∫ y, min y Q ∂ρ := by
  rw [← integral_sub (int_min ρ hint _) (int_min ρ hint _), ← real_Ioi, mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  exact integral_mono ((integrable_const _).indicator measurableSet_Ioi)
    ((int_min ρ hint _).sub (int_min ρ hint _)) (fun x => min_inc_lower x Q Q' h)

lemma inc_hi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q Q' : ℝ)
    (h : Q ≤ Q') :
    ∫ y, min y Q' ∂ρ - ∫ y, min y Q ∂ρ ≤ (Q' - Q) * (1 - cdf ρ Q) := by
  rw [← integral_sub (int_min ρ hint _) (int_min ρ hint _), ← real_Ioi, mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  exact integral_mono ((int_min ρ hint _).sub (int_min ρ hint _))
    ((integrable_const _).indicator measurableSet_Ioi) (fun x => min_inc_upper x Q Q' h)

/-- The newsvendor problem `max_Q a·E min(Y,Q) − b·Q + C` with `0 < b < a` and a continuous
distribution function: the optimal productions are exactly the solutions of
`F(Q) = 1 − b/a`, and one exists. -/
lemma newsvendor (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ)
    (hc : Continuous (cdf ρ)) (a b C : ℝ) (hb : 0 < b) (hba : b < a) :
    (∃ Q, cdf ρ Q = 1 - b / a) ∧
      ∀ Q, IsMaxOn (fun Q => a * ∫ y, min y Q ∂ρ - b * Q + C) univ Q ↔
        cdf ρ Q = 1 - b / a := by
  have ha : 0 < a := by linarith
  set k := 1 - b / a with hk
  have e1 : a * (1 - k) = b := by rw [hk]; field_simp; ring
  have hk0 : 0 < k := by
    rw [hk, sub_pos, div_lt_one ha]; exact hba
  have hk1 : k < 1 := by rw [hk]; have := div_pos hb ha; linarith
  refine ⟨?_, fun Q => ⟨fun hmax => ?_, fun hQ => ?_⟩⟩
  · obtain ⟨x0, hx0⟩ := ((tendsto_order.1 (tendsto_cdf_atBot ρ)).2 k hk0).exists
    obtain ⟨x1, hx1⟩ := ((tendsto_order.1 (tendsto_cdf_atTop ρ)).1 k hk1).exists
    obtain ⟨Q, hQ⟩ := intermediate_value_univ x0 x1 hc ⟨hx0.le, hx1.le⟩
    exact ⟨Q, hQ⟩
  · have hmax' := isMaxOn_iff.1 hmax
    -- right perturbations: `F(Q + δ) ≥ k`
    have hr : ∀ δ > 0, k ≤ cdf ρ (Q + δ) := by
      intro δ hδ
      have h1 := hmax' (Q + δ) (mem_univ _)
      have h2 := inc_lo ρ hint Q (Q + δ) (by linarith)
      have h3 := mul_le_mul_of_nonneg_left h2 ha.le
      have h4 : (a * (1 - cdf ρ (Q + δ))) * δ ≤ b * δ := by nlinarith
      have h5 := le_of_mul_le_mul_right h4 hδ
      have h6 : a * (1 - cdf ρ (Q + δ)) ≤ a * (1 - k) := by rw [e1]; exact h5
      have := le_of_mul_le_mul_left h6 ha
      linarith
    -- left perturbations: `F(Q − δ) ≤ k`
    have hl : ∀ δ > 0, cdf ρ (Q - δ) ≤ k := by
      intro δ hδ
      have h1 := hmax' (Q - δ) (mem_univ _)
      have h2 := inc_hi ρ hint (Q - δ) Q (by linarith)
      have h3 := mul_le_mul_of_nonneg_left h2 ha.le
      have h4 : b * δ ≤ (a * (1 - cdf ρ (Q - δ))) * δ := by nlinarith
      have h5 := le_of_mul_le_mul_right h4 hδ
      have h6 : a * (1 - k) ≤ a * (1 - cdf ρ (Q - δ)) := by rw [e1]; exact h5
      have := le_of_mul_le_mul_left h6 ha
      linarith
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have hev := (hc.tendsto Q).eventually (lt_mem_nhds hlt)
      rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
      have := hball (y := Q - ε / 2) (by
        rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
      have := hl (ε / 2) (by linarith)
      linarith
    · by_contra hlt
      push Not at hlt
      have hev := (hc.tendsto Q).eventually (gt_mem_nhds hlt)
      rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
      have := hball (y := Q + ε / 2) (by
        rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
      have := hr (ε / 2) (by linarith)
      linarith
  · rw [isMaxOn_iff]
    intro Q'' _
    rcases le_total Q Q'' with h | h
    · have h2 := inc_hi ρ hint Q Q'' h
      rw [hQ] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 ha.le
      have e2 : a * ((Q'' - Q) * (1 - k)) = b * (Q'' - Q) := by rw [← e1]; ring
      linarith
    · have h2 := inc_lo ρ hint Q'' Q h
      rw [hQ] at h2
      have h3 := mul_le_mul_of_nonneg_left h2 ha.le
      have e2 : a * ((Q - Q'') * (1 - k)) = b * (Q - Q'') := by rw [← e1]; ring
      linarith

end TsayQFNVAux

open TsayQF.NoCommit Set TsayQFNVAux in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D) :
    (∃ Q : ℝ, cdf ν (Q - z * Real.sqrt v) = kEM D) ∧
      ∀ Q : ℝ, IsMaxOn (emProfit D ν v z) Set.univ Q ↔
        cdf ν (Q - z * Real.sqrt v) = kEM D := by
  have hint : Integrable id ν := hν.integrable one_le_two
  set w := z * Real.sqrt v with hw
  set ρ := ν.map (fun μ => μ + w) with hρ
  have hprob : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hintρ : Integrable id ρ := by
    rw [hρ, integrable_map_measure (by fun_prop) (by fun_prop)]
    exact hint.add (integrable_const _)
  have hcdf : ∀ Q, cdf ρ Q = cdf ν (Q - w) := by
    intro Q
    rw [cdf_eq_real, cdf_eq_real, hρ, map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x; simp only [mem_preimage, mem_Iic]; constructor <;> intro h <;> linarith
  have hc : Continuous (cdf ρ) := by
    have : (cdf ρ : ℝ → ℝ) = fun Q => cdf ν (Q - w) := funext hcdf
    rw [this]; exact hΘd.continuous.comp (continuous_sub_right w)
  have hem : emProfit D ν v z =
      fun Q => (D.c - D.u) * ∫ y, min y Q ∂ρ - (D.m - D.u) * Q + 0 := by
    funext Q
    unfold emProfit ncPurchase
    rw [hρ, integral_map (by fun_prop) (by fun_prop), add_zero]
  have hkEM : kEM D = 1 - (D.m - D.u) / (D.c - D.u) := by
    have : 0 < D.c - D.u := by linarith [D.hmc, D.hum]
    unfold kEM; field_simp; ring
  obtain ⟨h1, h2⟩ := newsvendor ρ hintρ hc (D.c - D.u) (D.m - D.u) 0
    (by linarith [D.hum]) (by linarith [D.hmc])
  rw [hem, hkEM]
  refine ⟨?_, fun Q => ?_⟩
  · obtain ⟨Q, hQ⟩ := h1; exact ⟨Q, by rw [← hcdf]; exact hQ⟩
  · rw [h2 Q, hcdf]
