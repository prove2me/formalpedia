-- Prove2me | solution 1 for TsayQF.NoCommit.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T14:57:12.708695+00:00
-- url     : https://prove2.me/submissions/1a61de45-d43d-46b3-a1ca-de2ad281a8d4

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQFProp1Aux
open TsayQF.NoCommit Set

/-- The centralized one-period payoff `p·min[x,q] − s[x−q]⁺ + u[q−x]⁺`. -/
noncomputable def hpay (D : Data) (x q : ℝ) : ℝ :=
  D.p * min x q - D.s * max (x - q) 0 + D.u * max (q - x) 0

lemma hpay_eq (D : Data) (x q : ℝ) :
    hpay D x q = (D.p + D.s - D.u) * min x q + D.u * q - D.s * x := by
  unfold hpay
  rcases le_total x q with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma payoff_eq (D : Data) (x r : ℝ) : payoff D x r = hpay D x r - D.c * r := by
  unfold payoff hpay; ring

lemma min_inc_lower (x Q Q' : ℝ) (h : Q ≤ Q') :
    (Ioi Q').indicator (fun _ => Q' - Q) x ≤ min x Q' - min x Q := by
  by_cases hx : x ∈ Ioi Q'
  · rw [indicator_of_mem hx]
    have : Q' < x := hx
    rw [min_eq_right this.le, min_eq_right (by linarith)]
  · rw [indicator_of_notMem hx]
    have := min_le_min_left x h
    linarith

lemma min_inc_upper (y Q δ : ℝ) (hδ : 0 ≤ δ) :
    min y Q - min y (Q - δ) ≤ (Ioi (Q - δ)).indicator (fun _ => δ) y := by
  by_cases hy : y ∈ Ioi (Q - δ)
  · rw [indicator_of_mem hy]
    have : Q - δ < y := hy
    rw [min_eq_right this.le]
    have := min_le_right y Q
    linarith
  · rw [indicator_of_notMem hy]
    have : y ≤ Q - δ := not_lt.1 hy
    rw [min_eq_left this, min_eq_left (by linarith)]
    simp

lemma kfacts (D : Data) : 0 < kR D ∧ kR D < 1 ∧ 0 < kEM D ∧ kEM D < 1 ∧
    (1 - kR D) * (1 - kEM D) = 1 - kS D := by
  have hm := D.hm; have hmc := D.hmc; have hcp := D.hcp; have hum := D.hum; have hs := D.hs
  have h1 : 0 < D.p + D.s - D.u := by linarith
  have h2 : 0 < D.c - D.u := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold kR; apply div_pos <;> linarith
  · unfold kR; rw [div_lt_one h1]; linarith
  · unfold kEM; apply div_pos <;> linarith
  · unfold kEM; rw [div_lt_one h2]; linarith
  · unfold kR kEM kS; field_simp; ring

end TsayQFProp1Aux

namespace TsayQFProp1Aux
open TsayQF.NoCommit Set Filter Topology

lemma min_inc_upper' (μ a Q δ : ℝ) (hδ : 0 ≤ δ) :
    min (μ + a) Q - min (μ + a) (Q - δ) ≤ (Ioi (Q - a - δ)).indicator (fun _ => δ) μ := by
  have h := min_inc_upper (μ + a) Q δ hδ
  have e : (μ + a ∈ Ioi (Q - δ)) ↔ (μ ∈ Ioi (Q - a - δ)) := by
    simp only [mem_Ioi]; constructor <;> intro h <;> linarith
  by_cases hm : μ ∈ Ioi (Q - a - δ)
  · rw [indicator_of_mem hm]; rw [indicator_of_mem (e.2 hm)] at h; exact h
  · rw [indicator_of_notMem hm]; rw [indicator_of_notMem (fun h' => hm (e.1 h'))] at h; exact h

lemma real_Ioi (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν.real (Ioi x) = 1 - cdf ν x := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

lemma integrable_nc (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν)
    (v : ℝ≥0) (z Q : ℝ) : Integrable (fun μ => ncPurchase v z μ Q) ν := by
  have h1 : Integrable (fun μ : ℝ => μ + z * Real.sqrt v) ν := hint.add (integrable_const _)
  have := h1.inf (integrable_const Q)
  exact this

lemma em_foc (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hc : Continuous (cdf ν))
    (hint : Integrable id ν) (v : ℝ≥0) (z Qnc : ℝ)
    (hnc : IsMaxOn (emProfit D ν v z) Set.univ Qnc) :
    cdf ν (Qnc - z * Real.sqrt v) ≤ kEM D := by
  have hm := D.hm; have hmc := D.hmc; have hum := D.hum
  set t := Qnc - z * Real.sqrt v with ht
  have key : ∀ δ > 0, cdf ν (t - δ) ≤ kEM D := by
    intro δ hδ
    have h1 : emProfit D ν v z (Qnc - δ) ≤ emProfit D ν v z Qnc := isMaxOn_iff.1 hnc _ (mem_univ _)
    unfold emProfit at h1
    have h2 : ∫ μ, ncPurchase v z μ Qnc ∂ν - ∫ μ, ncPurchase v z μ (Qnc - δ) ∂ν ≤
        ν.real (Ioi (t - δ)) * δ := by
      rw [← integral_sub (integrable_nc ν hint v z _) (integrable_nc ν hint v z _)]
      calc ∫ μ, (ncPurchase v z μ Qnc - ncPurchase v z μ (Qnc - δ)) ∂ν
          ≤ ∫ μ, (Ioi (t - δ)).indicator (fun _ => δ) μ ∂ν := by
            apply integral_mono ((integrable_nc ν hint v z _).sub (integrable_nc ν hint v z _))
            · exact (integrable_const δ).indicator measurableSet_Ioi
            · intro μ
              have := min_inc_upper' μ (z * Real.sqrt v) Qnc δ hδ.le
              simpa [ncPurchase, ht] using this
        _ = ν.real (Ioi (t - δ)) * δ := by
            rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul]
    rw [real_Ioi] at h2
    have h3 : (D.m - D.u) * δ ≤ (D.c - D.u) * ((1 - cdf ν (t - δ)) * δ) := by
      have := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ D.c - D.u)
      nlinarith
    have h4 : D.m - D.u ≤ (D.c - D.u) * (1 - cdf ν (t - δ)) := by
      have : ((D.m - D.u) - (D.c - D.u) * (1 - cdf ν (t - δ))) * δ ≤ 0 := by nlinarith
      have := (mul_nonpos_iff.1 this)
      rcases this with ⟨_, h⟩ | ⟨h, _⟩
      · linarith
      · linarith
    unfold kEM
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  by_contra hlt
  push Not at hlt
  have hev := (hc.tendsto t).eventually (lt_mem_nhds hlt)
  rcases Metric.eventually_nhds_iff.1 hev with ⟨ε, hε, hball⟩
  have := hball (y := t - ε / 2) (by
    rw [Real.dist_eq]; rw [abs_of_neg (by linarith)]; linarith)
  have := key (ε / 2) (by linarith)
  linarith

lemma gauss_N (v : ℝ≥0) (hv : v ≠ 0) :
    (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp [Real.sq_sqrt (NNReal.coe_nonneg v)]

lemma gauss_cdf_z (D : Data) (v : ℝ≥0) (hv : v ≠ 0) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = kR D) :
    cdf (gaussianReal 0 v) (z * Real.sqrt v) = kR D := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 (by
    rcases (NNReal.coe_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm) hv)
  rw [cdf_eq_real, ← gauss_N v hv, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    ← hz, cdf_eq_real]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma gauss_AB (D : Data) (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D) :
    (∀ d > 0, cdf (gaussianReal 0 v) (z * Real.sqrt v - d) ≤ kR D) ∧
      cdf (gaussianReal 0 v) (z * Real.sqrt v - 1) < kR D := by
  obtain ⟨hk0, -, -, -, -⟩ := kfacts D
  by_cases hv : v = 0
  · subst hv
    have e : ∀ d > (0:ℝ), cdf (gaussianReal 0 0) (z * Real.sqrt ((0:ℝ≥0):ℝ) - d) = 0 := by
      intro d hd
      rw [gaussianReal_zero_var, cdf_eq_real]
      simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, zero_sub]
      rw [measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
      rw [indicator_of_notMem (by simp; linarith)]
      simp
    exact ⟨fun d hd => by rw [e d hd]; exact hk0.le, by rw [e 1 one_pos]; exact hk0⟩
  · have h0 := gauss_cdf_z D v hv z hz
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [← h0]; exact monotone_cdf _ (by linarith)
    · rw [← h0]
      have hpos : 0 < (gaussianReal 0 v) (Ioc (z * Real.sqrt v - 1) (z * Real.sqrt v)) := by
        rw [pos_iff_ne_zero]
        intro h
        have := gaussianReal_absolutelyContinuous' 0 hv h
        simp at this
      rw [← measure_cdf (gaussianReal 0 v), StieltjesFunction.measure_Ioc] at hpos
      have := ENNReal.ofReal_pos.1 hpos
      linarith

end TsayQFProp1Aux

namespace TsayQFProp1Aux
open TsayQF.NoCommit Set Filter Topology

lemma lawX_prob (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) :
    IsProbabilityMeasure (lawX ν v) := by
  unfold lawX; exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma lawX_Ioi (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) (Q : ℝ) :
    lawX ν v (Ioi Q) = ∫⁻ μ, gaussianReal 0 v (Ioi (Q - μ)) ∂ν := by
  unfold lawX
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi,
    Measure.prod_apply (measurableSet_Ioi.preimage (by fun_prop))]
  congr 1; funext μ; congr 1; ext ε
  simp only [mem_preimage, mem_Ioi]
  constructor <;> intro h <;> linarith

lemma ennreal_Ioi (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν (Ioi x) = ENNReal.ofReal (1 - cdf ν x) := by
  rw [← real_Ioi]; exact (ofReal_measureReal (measure_ne_top _ _)).symm

lemma real_Ioc (ν : Measure ℝ) [IsProbabilityMeasure ν] (a b : ℝ) (h : a ≤ b) :
    ν.real (Ioc a b) = cdf ν b - cdf ν a := by
  have e := StieltjesFunction.measure_Ioc (cdf ν) a b
  rw [measure_cdf] at e
  rw [measureReal_def, e, ENNReal.toReal_ofReal (sub_nonneg.2 (monotone_cdf ν h))]

lemma tail_strict (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D)
    (Qnc : ℝ) (hfoc : cdf ν (Qnc - z * Real.sqrt v) ≤ kEM D) :
    cdf (lawX ν v) Qnc < kS D := by
  have := lawX_prob ν v
  obtain ⟨hk0, hk1, -, -, hkk⟩ := kfacts D
  obtain ⟨hA, hB⟩ := gauss_AB D v z hz
  set t := Qnc - z * Real.sqrt v with ht
  set N := gaussianReal 0 v with hN
  set γ := 1 - cdf N (z * Real.sqrt v - 1) with hγ
  have hlow : ENNReal.ofReal (1 - kR D) * ν (Ioc t (t + 1)) + ENNReal.ofReal γ * ν (Ioi (t + 1))
      ≤ lawX ν v (Ioi Qnc) := by
    rw [lawX_Ioi, ← lintegral_indicator_const measurableSet_Ioc,
      ← lintegral_indicator_const measurableSet_Ioi,
      ← lintegral_add_left (measurable_const.indicator measurableSet_Ioc)]
    apply lintegral_mono
    intro μ
    dsimp only
    by_cases h1 : μ ∈ Ioc t (t + 1)
    · have h2 : μ ∉ Ioi (t + 1) := by simp only [mem_Ioi, not_lt]; exact h1.2
      rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero, ennreal_Ioi]
      apply ENNReal.ofReal_le_ofReal
      have := hA (μ - t) (by linarith [h1.1])
      have e : z * Real.sqrt v - (μ - t) = Qnc - μ := by rw [ht]; ring
      rw [e] at this; linarith
    · rw [indicator_of_notMem h1, zero_add]
      by_cases h2 : μ ∈ Ioi (t + 1)
      · rw [indicator_of_mem h2, ennreal_Ioi]
        apply ENNReal.ofReal_le_ofReal
        have : cdf N (Qnc - μ) ≤ cdf N (z * Real.sqrt v - 1) :=
          monotone_cdf N (by have : t + 1 < μ := h2; rw [ht] at this; linarith)
        linarith
      · rw [indicator_of_notMem h2]; exact bot_le
  have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hlow
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith), ← measureReal_def, ← measureReal_def, ← measureReal_def,
    real_Ioc ν t (t + 1) (by linarith), real_Ioi, real_Ioi] at hreal
  have hF1 : cdf ν (t + 1) < 1 := lt_of_lt_of_le (hΘ (by linarith : t + 1 < t + 2)) (cdf_le_one _ _)
  have hFt : cdf ν t ≤ cdf ν (t + 1) := monotone_cdf ν (by linarith)
  have hg : 1 - kR D < γ := by linarith
  nlinarith [mul_pos (sub_pos.2 hg) (sub_pos.2 hF1),
    mul_le_mul_of_nonneg_left hfoc (by linarith : (0:ℝ) ≤ 1 - kR D)]

end TsayQFProp1Aux

namespace TsayQFProp1Aux
open TsayQF.NoCommit Set Filter Topology

lemma int_gauss (v : ℝ≥0) : Integrable id (gaussianReal 0 v) :=
  (memLp_id_gaussianReal' (μ := 0) (v := v) 1 ENNReal.one_ne_top).integrable le_rfl

lemma int_X (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν) (v : ℝ≥0) :
    Integrable (fun w : ℝ × ℝ => w.1 + w.2) (ν.prod (gaussianReal 0 v)) :=
  (hint.comp_fst _).add ((int_gauss v).comp_snd _)

lemma int_lawX (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν) (v : ℝ≥0) :
    Integrable id (lawX ν v) := by
  unfold lawX
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  exact int_X ν hint v

lemma int_hpay (D : Data) {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    (f g : α → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun w => hpay D (f w) (g w)) P := by
  simp_rw [hpay_eq]
  have h1 : Integrable (fun w => min (f w) (g w)) P := hf.inf hg
  exact ((h1.const_mul _).add (hg.const_mul _)).sub (hf.const_mul _)

lemma cc_eq (D : Data) (ν : Measure ℝ) (v : ℝ≥0) (Q : ℝ) :
    ccProfit D ν v Q = ∫ x, hpay D x Q ∂(lawX ν v) - D.m * Q := rfl

lemma cc_inc (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν)
    (v : ℝ≥0) (Q Q' : ℝ) (h : Q ≤ Q') :
    (Q' - Q) * ((D.p + D.s - D.u) * (lawX ν v).real (Ioi Q') - (D.m - D.u)) ≤
      ccProfit D ν v Q' - ccProfit D ν v Q := by
  have := lawX_prob ν v
  have hX := int_lawX ν hint v
  have hk : 0 ≤ D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
  have i1 := int_hpay D (lawX ν v) id (fun _ => Q') hX (integrable_const _)
  have i0 := int_hpay D (lawX ν v) id (fun _ => Q) hX (integrable_const _)
  have hmain : ∫ x, ((D.p + D.s - D.u) * (Ioi Q').indicator (fun _ => Q' - Q) x
      + D.u * (Q' - Q)) ∂(lawX ν v) ≤ ∫ x, (hpay D x Q' - hpay D x Q) ∂(lawX ν v) := by
    apply integral_mono
    · exact (((integrable_const _).indicator measurableSet_Ioi).const_mul _).add
        (integrable_const _)
    · exact i1.sub i0
    · intro x
      dsimp only
      rw [hpay_eq, hpay_eq]
      have := min_inc_lower x Q Q' h
      nlinarith [mul_le_mul_of_nonneg_left this hk]
  rw [integral_add (((integrable_const _).indicator measurableSet_Ioi).const_mul _)
      (integrable_const _), integral_const_mul, integral_indicator_const _ measurableSet_Ioi,
    integral_const] at hmain
  rw [show (∫ x, (hpay D x Q' - hpay D x Q) ∂lawX ν v) = _ from integral_sub i1 i0] at hmain
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmain
  rw [cc_eq, cc_eq]
  nlinarith

lemma G_eq (D : Data) (v : ℝ≥0) (r μ : ℝ) :
    G D v r μ = ∫ ε, payoff D (μ + ε) r ∂(gaussianReal 0 v) := by
  unfold G
  have := gaussianReal_map_const_add (μ := 0) (v := v) μ
  rw [zero_add] at this
  rw [← this, integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by unfold payoff; fun_prop))]

lemma sys_le (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν)
    (v : ℝ≥0) (z Q : ℝ) : systemProfit D ν v z Q ≤ ccProfit D ν v Q := by
  set N := gaussianReal 0 v with hN
  set P := ν.prod N with hP
  have hXi := int_X ν hint v
  have hfst : Integrable (fun w : ℝ × ℝ => w.1) P := hint.comp_fst _
  have hr : Integrable (fun w : ℝ × ℝ => ncPurchase v z w.1 Q) P :=
    (integrable_nc ν hint v z Q).comp_fst _
  have hg : Integrable (fun w : ℝ × ℝ => payoff D (w.1 + w.2) (ncPurchase v z w.1 Q)) P := by
    simp_rw [payoff_eq]
    exact (int_hpay D P _ _ hXi hr).sub (hr.const_mul _)
  have hH : Integrable (fun w : ℝ × ℝ => hpay D (w.1 + w.2) Q) P :=
    int_hpay D P _ _ hXi (integrable_const _)
  -- the three integrals as integrals over the product
  have eR : retailerProfit D ν v z Q =
      ∫ w, payoff D (w.1 + w.2) (ncPurchase v z w.1 Q) ∂P := by
    rw [integral_prod _ hg]
    unfold retailerProfit
    simp_rw [G_eq]
    rfl
  have eE : ∫ μ, ncPurchase v z μ Q ∂ν = ∫ w, ncPurchase v z w.1 Q ∂P := by
    rw [integral_prod _ hr]
    simp
  have eC : ∫ x, hpay D x Q ∂(lawX ν v) = ∫ w, hpay D (w.1 + w.2) Q ∂P := by
    unfold lawX
    rw [integral_map (by fun_prop)
      (Continuous.aestronglyMeasurable (by simp_rw [hpay_eq]; fun_prop))]
  have hmain : ∫ w, (payoff D (w.1 + w.2) (ncPurchase v z w.1 Q)
      + (D.c - D.u) * ncPurchase v z w.1 Q) ∂P ≤ ∫ w, (hpay D (w.1 + w.2) Q - D.u * Q) ∂P := by
    apply integral_mono (hg.add (hr.const_mul _)) (hH.sub (integrable_const _))
    intro w
    simp only [Pi.add_apply, Pi.sub_apply]
    have hle : ncPurchase v z w.1 Q ≤ Q := min_le_right _ _
    rw [payoff_eq, hpay_eq, hpay_eq]
    have hk : 0 ≤ D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
    have := min_le_min_left (w.1 + w.2) hle
    nlinarith [mul_le_mul_of_nonneg_left this hk]
  rw [integral_add hg (hr.const_mul _), integral_const_mul, integral_sub hH (integrable_const _),
    integral_const] at hmain
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmain
  unfold systemProfit emProfit
  rw [cc_eq, eR, eE, eC]
  nlinarith

end TsayQFProp1Aux

open TsayQF.NoCommit Set Filter Topology TsayQFProp1Aux in
theorem solution (D : Data) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hΘ : StrictMono (cdf ν)) (hΘd : Differentiable ℝ (cdf ν)) (hν : MemLp id 2 ν)
    (v : ℝ≥0) (z : ℝ) (hz : cdf (gaussianReal 0 1) z = kR D) (Qnc Qcc : ℝ)
    (hnc : IsMaxOn (emProfit D ν v z) Set.univ Qnc)
    (hcc : IsMaxOn (ccProfit D ν v) Set.univ Qcc) :
    Qnc < Qcc ∧ systemProfit D ν v z Qnc < ccProfit D ν v Qcc := by
  have := lawX_prob ν v
  have hint : Integrable id ν := hν.integrable one_le_two
  have hfoc := em_foc D ν hΘd.continuous hint v z Qnc hnc
  have hF := tail_strict D ν hΘ v z hz Qnc hfoc
  have ev : ∀ᶠ x in 𝓝[Ici Qnc] Qnc, cdf (lawX ν v) x < kS D :=
    ((cdf (lawX ν v)).right_continuous Qnc).eventually (gt_mem_nhds hF)
  have ev' : ∀ᶠ x in 𝓝[>] Qnc, cdf (lawX ν v) x < kS D :=
    ev.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  obtain ⟨Q', hQ'2, hQ'1⟩ := (ev'.and self_mem_nhdsWithin).exists
  have hQ'1 : Qnc < Q' := hQ'1
  have hks : (D.p + D.s - D.u) * (1 - kS D) = D.m - D.u := by
    have : 0 < D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
    unfold kS; field_simp; ring
  have hk : 0 < D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
  have hgap : 0 < (D.p + D.s - D.u) * (lawX ν v).real (Ioi Q') - (D.m - D.u) := by
    rw [real_Ioi]; nlinarith
  have hstrict : ∀ Q < Q', ccProfit D ν v Q < ccProfit D ν v Q' := by
    intro Q hQ
    have := cc_inc D ν hint v Q Q' hQ.le
    have := mul_pos (sub_pos.2 hQ) hgap
    linarith
  have hmax : ccProfit D ν v Q' ≤ ccProfit D ν v Qcc := isMaxOn_iff.1 hcc _ (mem_univ _)
  have h1 : Qnc < Qcc := by
    by_contra hle
    push Not at hle
    have := hstrict Qcc (lt_of_le_of_lt hle hQ'1)
    linarith
  refine ⟨h1, ?_⟩
  have := sys_le D ν hint v z Qnc
  have := hstrict Qnc hQ'1
  linarith
