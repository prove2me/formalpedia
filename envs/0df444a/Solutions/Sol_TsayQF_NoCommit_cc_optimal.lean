-- Prove2me | solution 1 for TsayQF.NoCommit.cc_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:03:25.546968+00:00
-- url     : https://prove2.me/submissions/acc96421-7589-40c6-ab31-8fcd10488dc7

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQFCCAux
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


open TsayQF.NoCommit

/-- The centralized one-period payoff `p·min[x,q] − s[x−q]⁺ + u[q−x]⁺`. -/
noncomputable def hpay (D : Data) (x q : ℝ) : ℝ :=
  D.p * min x q - D.s * max (x - q) 0 + D.u * max (q - x) 0

lemma hpay_eq (D : Data) (x q : ℝ) :
    hpay D x q = (D.p + D.s - D.u) * min x q + D.u * q - D.s * x := by
  unfold hpay
  rcases le_total x q with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma lawX_prob (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) :
    IsProbabilityMeasure (lawX ν v) := by
  unfold lawX; exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma int_gauss (v : ℝ≥0) : Integrable id (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 ENNReal.one_ne_top).integrable le_rfl

lemma int_lawX (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν) (v : ℝ≥0) :
    Integrable id (lawX ν v) := by
  unfold lawX
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  exact (hint.comp_fst _).add ((int_gauss v).comp_snd _)

lemma cont_of_atomless (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (h : ∀ x, ρ {x} = 0) :
    Continuous (cdf ρ) := by
  rw [continuous_iff_continuousAt]; intro x
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf ρ).right_continuous x⟩
  rw [← continuousWithinAt_Iio_iff_Iic,
    Monotone.continuousWithinAt_Iio_iff_leftLim_eq (cdf ρ).mono]
  have h1 := (cdf ρ).measure_singleton x
  rw [measure_cdf, h x] at h1
  have h2 := ENNReal.ofReal_eq_zero.1 h1.symm
  have h3 : Function.leftLim (cdf ρ) x ≤ cdf ρ x := (cdf ρ).mono.leftLim_le le_rfl
  linarith

lemma lawX_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν] (hc : Continuous (cdf ν))
    (v : ℝ≥0) (x : ℝ) : lawX ν v {x} = 0 := by
  have hatom : ∀ a, ν {a} = 0 := by
    intro a
    have h1 := (cdf ν).measure_singleton a
    rw [measure_cdf, (hc.continuousAt.continuousWithinAt).leftLim_eq, sub_self,
      ENNReal.ofReal_zero] at h1
    exact h1
  unfold lawX
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton x),
    Measure.prod_apply_symm ((measurableSet_singleton x).preimage (by fun_prop))]
  have e : ∀ ε : ℝ, (fun μ : ℝ => (μ, ε)) ⁻¹' ((fun w : ℝ × ℝ => w.1 + w.2) ⁻¹' {x}) =
      {x - ε} := by
    intro ε; ext μ; simp only [mem_preimage, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  simp_rw [e, hatom, lintegral_zero]

end TsayQFCCAux

open TsayQF.NoCommit Set TsayQFCCAux in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) :
    (∃ Q : ℝ, cdf (lawX ν v) Q = kS D) ∧
      ∀ Q : ℝ, IsMaxOn (ccProfit D ν v) Set.univ Q ↔ cdf (lawX ν v) Q = kS D := by
  have hint : Integrable id ν := hν.integrable one_le_two
  have hprob := lawX_prob ν v
  have hX := int_lawX ν hint v
  have hc := cont_of_atomless (lawX ν v) (lawX_atomless ν hΘd.continuous v)
  have hcc : ccProfit D ν v = fun Q => (D.p + D.s - D.u) * ∫ x, min x Q ∂(lawX ν v)
      - (D.m - D.u) * Q + (-(D.s * ∫ x, x ∂(lawX ν v))) := by
    funext Q
    have hm := int_min (lawX ν v) hX Q
    have e : ccProfit D ν v Q = ∫ x, hpay D x Q ∂(lawX ν v) - D.m * Q := rfl
    rw [e]
    simp_rw [hpay_eq]
    have i1 : Integrable (fun x => (D.p + D.s - D.u) * min x Q + D.u * Q) (lawX ν v) :=
      (hm.const_mul _).add (integrable_const _)
    have i2 : Integrable (fun x : ℝ => D.s * x) (lawX ν v) := hX.const_mul _
    rw [integral_sub i1 i2,
      integral_add (hm.const_mul _) (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [integral_const_mul]
    ring
  have hkS : kS D = 1 - (D.m - D.u) / (D.p + D.s - D.u) := by
    have : 0 < D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
    unfold kS; field_simp; ring
  obtain ⟨h1, h2⟩ := newsvendor (lawX ν v) hX hc (D.p + D.s - D.u) (D.m - D.u) _
    (by linarith [D.hum]) (by linarith [D.hmc, D.hcp, D.hs])
  rw [hcc, hkS]
  exact ⟨h1, h2⟩
