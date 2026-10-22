-- Prove2me | solution 1 for TokenICO.UtilityEq.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:24:52.995722+00:00
-- url     : https://prove2.me/submissions/4bc20bbd-4ffc-4aa2-b757-5ccc4a015496

import Mathlib
import Definitions.Def_TokenICO_UtilityEq_Setting

open MeasureTheory ProbabilityTheory

namespace TokenICO.UtilityEq.P3Aux

open Set

variable {m c v z : ℝ} {μ : Measure ℝ} {f f' : ℝ → ℝ}

lemma ae_pos (h : Standing m c v z μ f f') : ∀ᵐ x ∂μ, 0 < x := by
  haveI := h.probability
  have h0 : μ (Iic 0) = 0 := by
    have := cdf_eq_real μ 0
    rw [h.cdf_nonpositive 0 le_rfl] at this
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this.symm
  rw [ae_iff]
  convert h0 using 2
  ext x; simp

lemma integrable_min (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 ≤ Q) :
    Integrable (fun x => min x Q) μ := by
  haveI := h.probability
  refine Integrable.of_bound
    ((continuous_id.min continuous_const).aestronglyMeasurable) Q ?_
  filter_upwards [ae_pos h] with x hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [le_min hx.le hQ], min_le_right _ _⟩

lemma ES_zero (h : Standing m c v z μ f f') : ES μ 0 = 0 := by
  unfold ES
  rw [integral_eq_zero_iff_of_nonneg_ae]
  · filter_upwards [ae_pos h] with x hx
    simp [min_eq_right hx.le]
  · filter_upwards [ae_pos h] with x hx
    simp [min_eq_right hx.le]
  · exact integrable_min h le_rfl

lemma real_Ioi (h : Standing m c v z μ f f') (a : ℝ) :
    μ.real (Ioi a) = 1 - cdf μ a := by
  haveI := h.probability
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

lemma real_Ioc (h : Standing m c v z μ f f') {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ioc a b) = cdf μ b - cdf μ a := by
  haveI := h.probability
  have hs : Ioc a b = Iic b \ Iic a := by ext x; simp [and_comm, not_le]
  rw [hs, measureReal_sdiff (Iic_subset_Iic.2 hab) measurableSet_Iic,
    cdf_eq_real, cdf_eq_real]

lemma ES_sub (h : Standing m c v z μ f f') {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQ' : 0 ≤ Q') :
    ES μ Q' - ES μ Q = ∫ x, (min x Q' - min x Q) ∂μ := by
  unfold ES
  rw [integral_sub (integrable_min h hQ') (integrable_min h hQ)]

lemma ES_upper (h : Standing m c v z μ f f') {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q < Q') :
    ES μ Q' - ES μ Q ≤ (Q' - Q) * (1 - cdf μ Q)
      - (Q' - Q) / 2 * (cdf μ ((Q + Q') / 2) - cdf μ Q) := by
  haveI := h.probability
  set M := (Q + Q') / 2 with hM
  have hQM : Q ≤ M := by rw [hM]; linarith
  rw [ES_sub h hQ (by linarith)]
  have hi1 : Integrable ((Ioi M).indicator (fun _ => Q' - Q)) μ :=
    (integrable_const _).indicator measurableSet_Ioi
  have hi2 : Integrable ((Ioc Q M).indicator (fun _ => (Q' - Q) / 2)) μ :=
    (integrable_const _).indicator measurableSet_Ioc
  have hle : ∫ x, (min x Q' - min x Q) ∂μ ≤
      ∫ x, ((Ioi M).indicator (fun _ => Q' - Q) x +
        (Ioc Q M).indicator (fun _ => (Q' - Q) / 2) x) ∂μ := by
    apply integral_mono ((integrable_min h (by linarith)).sub (integrable_min h hQ))
      (hi1.add hi2)
    intro x
    simp only [Pi.add_apply, Pi.sub_apply, indicator, mem_Ioi, mem_Ioc]
    by_cases h1 : M < x
    · have : ¬ (Q < x ∧ x ≤ M) := fun hh => by linarith [hh.2]
      rw [if_pos h1, if_neg this]
      have := min_le_right x Q'
      have : Q ≤ min x Q ∨ True := Or.inr trivial
      rcases le_total x Q with hx | hx
      · rw [min_eq_left hx, min_eq_left (by linarith)]; linarith
      · rw [min_eq_right hx]; linarith [min_le_right x Q']
    · rw [if_neg h1]
      by_cases h2 : Q < x
      · rw [if_pos ⟨h2, le_of_not_gt h1⟩, min_eq_right h2.le]
        have : x ≤ M := le_of_not_gt h1
        linarith [min_le_left x Q']
      · rw [if_neg (fun hh => h2 hh.1)]
        push_neg at h2
        rw [min_eq_left h2, min_eq_left (by linarith)]; simp
  refine hle.trans (le_of_eq ?_)
  rw [integral_add hi1 hi2, integral_indicator_const _ measurableSet_Ioi,
    integral_indicator_const _ measurableSet_Ioc, real_Ioi h, real_Ioc h hQM]
  simp only [smul_eq_mul]
  have : cdf μ M ≤ 1 := cdf_le_one μ M
  ring

lemma ES_lower (h : Standing m c v z μ f f') {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q < Q') :
    (Q' - Q) * (1 - cdf μ Q') + (Q' - Q) / 2 * (cdf μ Q' - cdf μ ((Q + Q') / 2))
      ≤ ES μ Q' - ES μ Q := by
  haveI := h.probability
  set M := (Q + Q') / 2 with hM
  have hMQ : M ≤ Q' := by rw [hM]; linarith
  have hQM : Q ≤ M := by rw [hM]; linarith
  rw [ES_sub h hQ (by linarith)]
  have hi1 : Integrable ((Ioi Q').indicator (fun _ => Q' - Q)) μ :=
    (integrable_const _).indicator measurableSet_Ioi
  have hi2 : Integrable ((Ioc M Q').indicator (fun _ => (Q' - Q) / 2)) μ :=
    (integrable_const _).indicator measurableSet_Ioc
  have hle : ∫ x, ((Ioi Q').indicator (fun _ => Q' - Q) x +
        (Ioc M Q').indicator (fun _ => (Q' - Q) / 2) x) ∂μ ≤
      ∫ x, (min x Q' - min x Q) ∂μ := by
    apply integral_mono (hi1.add hi2)
      ((integrable_min h (by linarith)).sub (integrable_min h hQ))
    intro x
    simp only [Pi.add_apply, Pi.sub_apply, indicator, mem_Ioi, mem_Ioc]
    by_cases h1 : Q' < x
    · have : ¬ (M < x ∧ x ≤ Q') := fun hh => by linarith [hh.2]
      rw [if_pos h1, if_neg this, min_eq_right h1.le, min_eq_right (by linarith)]
      linarith
    · rw [if_neg h1]
      push_neg at h1
      by_cases h2 : M < x
      · rw [if_pos ⟨h2, h1⟩, min_eq_left h1, min_eq_right (by linarith)]
        linarith
      · rw [if_neg (fun hh => h2 hh.1)]
        push_neg at h2
        rw [min_eq_left h1]
        rcases le_total x Q with hx | hx
        · rw [min_eq_left hx]; simp
        · rw [min_eq_right hx]; linarith
  refine le_trans (le_of_eq ?_) hle
  rw [integral_add hi1 hi2, integral_indicator_const _ measurableSet_Ioi,
    integral_indicator_const _ measurableSet_Ioc, real_Ioi h, real_Ioc h hMQ]
  simp only [smul_eq_mul]
  ring

lemma F_strict (h : Standing m c v z μ f f') {x x' : ℝ} (hx : 0 ≤ x) (hxx : x < x')
    (h1 : cdf μ x < 1) : cdf μ x < cdf μ x' := by
  rcases hx.eq_or_lt with rfl | hx0
  · rw [h.cdf_nonpositive 0 le_rfl]; exact h.cdf_positive x' hxx
  · obtain ⟨hd, hf, -⟩ := h.density x hx0 h1
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    have hev : ∀ᶠ y in nhdsWithin x (Ioi x), 0 < slope (cdf μ) x y :=
      (ht.mono_left (nhdsWithin_mono _ (fun y (hy : x < y) =>
        mem_compl_singleton_iff.2 (ne_of_gt hy)))).eventually (lt_mem_nhds hf)
    obtain ⟨y, hy, hyI⟩ := (hev.and (Ioo_mem_nhdsGT hxx)).exists
    rw [slope_def_field] at hy
    have hyx : 0 < y - x := by linarith [hyI.1]
    have : 0 < cdf μ y - cdf μ x := (div_pos_iff_of_pos_right hyx).1 hy
    linarith [monotone_cdf μ hyI.2.le]

lemma F_lt_rev {a b : ℝ} (hab : cdf μ a < cdf μ b) : a < b := by
  by_contra hh; push_neg at hh; linarith [monotone_cdf μ hh]

lemma Finv_spec (h : Standing m c v z μ f f') {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    0 < Finv μ y ∧ cdf μ (Finv μ y) = y := by
  haveI := h.probability
  set S := {x : ℝ | 0 ≤ x ∧ y ≤ cdf μ x} with hS
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hy1)).and
      (Filter.eventually_ge_atTop 0)).exists
    exact ⟨x, hx.2, hx.1.le⟩
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const h.cdf_continuous)
  have hmem : sInf S ∈ S := hclosed.csInf_mem hne hbdd
  have hq : Finv μ y = sInf S := rfl
  rw [hq]
  have hpos : 0 < sInf S := by
    rcases hmem.1.eq_or_lt with h0 | h0
    · exfalso; have := hmem.2; rw [← h0, h.cdf_nonpositive 0 le_rfl] at this; linarith
    · exact h0
  refine ⟨hpos, le_antisymm ?_ hmem.2⟩
  by_contra hlt; push_neg at hlt
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hpos.le h.cdf_continuous.continuousOn
    ⟨by rw [h.cdf_nonpositive 0 le_rfl]; exact hy0.le, hlt.le⟩
  have : sInf S ≤ x := csInf_le hbdd ⟨hx.1, hFx.ge⟩
  have hxq : x = sInf S := le_antisymm hx.2 this
  rw [hxq] at hFx; linarith

lemma Finv_F (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 < Q) (h1 : cdf μ Q < 1) :
    Finv μ (cdf μ Q) = Q := by
  obtain ⟨hq0, hq⟩ := Finv_spec h (h.cdf_positive Q hQ) h1
  rcases lt_trichotomy (Finv μ (cdf μ Q)) Q with hl | he | hl
  · have := F_strict h hq0.le hl (by rw [hq]; exact h1); linarith
  · exact he
  · have := F_strict h hQ.le hl h1; linarith

lemma ES_nonneg (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 ≤ Q) : 0 ≤ ES μ Q := by
  rcases hQ.eq_or_lt with rfl | hQ0
  · rw [ES_zero h]
  · have := ES_lower h le_rfl hQ0
    rw [ES_zero h] at this
    have h1 := cdf_le_one μ Q
    have h2 := monotone_cdf μ (show (0 + Q) / 2 ≤ Q by linarith)
    nlinarith

lemma ES_lt (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 < Q) : ES μ Q < Q := by
  have := ES_upper h le_rfl hQ
  rw [ES_zero h, h.cdf_nonpositive 0 le_rfl] at this
  have h2 := h.cdf_positive ((0 + Q) / 2) (by linarith)
  nlinarith

lemma ES_le (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 ≤ Q) : ES μ Q ≤ Q := by
  rcases hQ.eq_or_lt with rfl | hQ0
  · rw [ES_zero h]
  · exact (ES_lt h hQ0).le

lemma ES_gt (h : Standing m c v z μ f f') {Q : ℝ} (hQ : 0 < Q) (h1 : cdf μ Q < 1) :
    Q * (1 - cdf μ Q) < ES μ Q := by
  have := ES_lower h le_rfl hQ
  rw [ES_zero h] at this
  have h2 := F_strict h (show 0 ≤ (0 + Q) / 2 by linarith) (show (0 + Q) / 2 < Q by linarith)
    (lt_of_le_of_lt (monotone_cdf μ (show (0 + Q) / 2 ≤ Q by linarith)) h1)
  nlinarith

lemma ES_mono (h : Standing m c v z μ f f') {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') :
    ES μ Q ≤ ES μ Q' := by
  rcases hQQ.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have := ES_lower h hQ hlt
    have h1 := cdf_le_one μ Q'
    have h2 := monotone_cdf μ (show (Q + Q') / 2 ≤ Q' by linarith)
    nlinarith

lemma ES_lip (h : Standing m c v z μ f f') {Q Q' : ℝ} (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') :
    ES μ Q' - ES μ Q ≤ Q' - Q := by
  rcases hQQ.eq_or_lt with rfl | hlt
  · simp
  · have := ES_upper h hQ hlt
    have h1 := cdf_nonneg μ Q
    have h2 := monotone_cdf μ (show Q ≤ (Q + Q') / 2 by linarith)
    nlinarith

lemma ES_contOn (h : Standing m c v z μ f f') : ContinuousOn (ES μ) (Ici 0) := by
  refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · have := ES_lip h (mem_Ici.1 hx) hxy
    have := ES_mono h (mem_Ici.1 hx) hxy
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have := ES_lip h (mem_Ici.1 hy) hxy
    have := ES_mono h (mem_Ici.1 hy) hxy
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

lemma ES_ratio (h : Standing m c v z μ f f') {Qa Qb : ℝ} (ha : 0 < Qa) (hab : Qa < Qb)
    (h1 : cdf μ Qa < 1) : Qa * ES μ Qb < Qb * ES μ Qa := by
  have hu := ES_upper h ha.le hab
  have h2 := monotone_cdf μ (show Qa ≤ (Qa + Qb) / 2 by linarith)
  have hg := ES_gt h ha h1
  have hu' : ES μ Qb - ES μ Qa ≤ (Qb - Qa) * (1 - cdf μ Qa) := by nlinarith
  have e1 : Qa * (ES μ Qb - ES μ Qa) ≤ Qa * ((Qb - Qa) * (1 - cdf μ Qa)) :=
    mul_le_mul_of_nonneg_left hu' ha.le
  have e2 : (Qb - Qa) * (Qa * (1 - cdf μ Qa)) < (Qb - Qa) * ES μ Qa :=
    mul_lt_mul_of_pos_left hg (by linarith)
  nlinarith

lemma G_inc (h : Standing m c v z μ f f') {a Q Q' Q0 : ℝ} (ha : 0 < a) (hQ : 0 ≤ Q)
    (hQQ : Q < Q') (hQ'0 : Q' ≤ Q0) (hF0 : cdf μ Q0 < 1)
    (hcond : c ≤ a * (1 - cdf μ Q0)) :
    a * ES μ Q - c * Q < a * ES μ Q' - c * Q' := by
  have hl := ES_lower h hQ hQQ
  have hFQ' := monotone_cdf μ hQ'0
  have hM : cdf μ ((Q + Q') / 2) < cdf μ Q' :=
    F_strict h (by linarith) (by linarith)
      (lt_of_le_of_lt (monotone_cdf μ (show (Q + Q') / 2 ≤ Q0 by linarith)) hF0)
  have e1 : a * ((Q' - Q) * (1 - cdf μ Q0)) ≤ a * ((Q' - Q) * (1 - cdf μ Q')) := by
    apply mul_le_mul_of_nonneg_left _ ha.le
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have e2 : 0 < a * ((Q' - Q) / 2 * (cdf μ Q' - cdf μ ((Q + Q') / 2))) :=
    mul_pos ha (mul_pos (by linarith) (by linarith))
  have e3 : c * (Q' - Q) ≤ a * ((Q' - Q) * (1 - cdf μ Q0)) := by
    have := mul_le_mul_of_nonneg_left hcond (show 0 ≤ Q' - Q by linarith)
    nlinarith
  have e4 := mul_le_mul_of_nonneg_left hl ha.le
  nlinarith

lemma G_dec (h : Standing m c v z μ f f') {a Q Q' Q0 : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hQ0 : 0 ≤ Q0) (hQ0Q : Q0 ≤ Q) (hQQ : Q < Q')
    (hcond : a * (1 - cdf μ Q0) ≤ c) :
    a * ES μ Q' - c * Q' < a * ES μ Q - c * Q := by
  have hQ : 0 ≤ Q := hQ0.trans hQ0Q
  have hu := ES_upper h hQ hQQ
  have hFQ := monotone_cdf μ hQ0Q
  have hFM := monotone_cdf μ (show Q ≤ (Q + Q') / 2 by linarith)
  have hF1 := cdf_le_one μ Q
  rcases ha.eq_or_lt with ha0 | ha0
  · rw [← ha0]; nlinarith
  have e4 := mul_le_mul_of_nonneg_left hu ha
  have e5 : 0 ≤ a * ((Q' - Q) / 2 * (cdf μ ((Q + Q') / 2) - cdf μ Q)) :=
    mul_nonneg ha (mul_nonneg (by linarith) (by linarith))
  have e6 : a * ((Q' - Q) * (1 - cdf μ Q)) ≤ c * (Q' - Q) := by
    have : a * (1 - cdf μ Q) ≤ c := by nlinarith
    nlinarith
  rcases hF1.lt_or_eq with hF1 | hF1
  · have hM : cdf μ Q < cdf μ ((Q + Q') / 2) := F_strict h hQ (by linarith) hF1
    have e5' : 0 < a * ((Q' - Q) / 2 * (cdf μ ((Q + Q') / 2) - cdf μ Q)) :=
      mul_pos ha0 (mul_pos (by linarith) (by linarith))
    nlinarith
  · have e7 : a * ((Q' - Q) * (1 - cdf μ Q)) = 0 := by rw [hF1]; ring
    have : 0 < c * (Q' - Q) := mul_pos hc (by linarith)
    nlinarith

lemma prodObj_eq (s Q : ℝ) :
    prodObj m c v μ s Q = (m - s) * (v / m) * ES μ Q - c * Q := by
  unfold prodObj; ring

lemma maxQ_le (h : Standing m c v z μ f f') {Qr : ℝ → ℝ → ℝ}
    (hQr : ProdOptimal m c v μ Qr) {τ s Q0 : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) (hsm : s ≤ m)
    (hQ0 : 0 ≤ Q0) (hQ0B : Q0 ≤ τ * s / c)
    (hcond : (m - s) * (v / m) * (1 - cdf μ Q0) ≤ c) : Qr τ s ≤ Q0 := by
  have hm := h.tokens_pos
  have hv0 : 0 < v := by linarith [h.value_gt_cost, h.cost_pos]
  obtain ⟨hmem, hmax⟩ := hQr τ s hτ hs hsm
  by_contra hlt; push_neg at hlt
  have := G_dec h (a := (m - s) * (v / m)) (Q := Q0) (Q' := Qr τ s) (Q0 := Q0)
    (mul_nonneg (by linarith) (by positivity)) h.cost_pos hQ0 le_rfl hlt hcond
  have h2 := isMaxOn_iff.1 hmax Q0 ⟨hQ0, hQ0B⟩
  rw [prodObj_eq, prodObj_eq] at h2
  linarith

lemma maxQ_ge (h : Standing m c v z μ f f') {Qr : ℝ → ℝ → ℝ}
    (hQr : ProdOptimal m c v μ Qr) {τ s Q0 : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s) (hsm : s < m)
    (hQ0 : 0 < Q0) (hQ0B : Q0 ≤ τ * s / c) (hF1 : cdf μ Q0 < 1)
    (hcond : c ≤ (m - s) * (v / m) * (1 - cdf μ Q0)) : Q0 ≤ Qr τ s := by
  have hm := h.tokens_pos
  have hv0 : 0 < v := by linarith [h.value_gt_cost, h.cost_pos]
  obtain ⟨hmem, hmax⟩ := hQr τ s hτ hs hsm.le
  by_contra hlt; push_neg at hlt
  have := G_inc h (a := (m - s) * (v / m)) (Q := Qr τ s) (Q' := Q0) (Q0 := Q0)
    (mul_pos (by linarith) (by positivity)) hmem.1 hlt le_rfl hF1 hcond
  have h2 := isMaxOn_iff.1 hmax Q0 ⟨hQ0.le, hQ0B⟩
  rw [prodObj_eq, prodObj_eq] at h2
  linarith

lemma exists_prodOptimal (h : Standing m c v z μ f f') :
    ∃ Qr : ℝ → ℝ → ℝ, ProdOptimal m c v μ Qr := by
  have hex : ∀ τ s : ℝ, ∃ Q : ℝ, 0 ≤ τ → 0 ≤ s → s ≤ m →
      (Q ∈ Icc 0 (τ * s / c) ∧ IsMaxOn (prodObj m c v μ s) (Icc 0 (τ * s / c)) Q) := by
    intro τ s
    by_cases hb : 0 ≤ τ * s / c
    · have hcont : ContinuousOn (prodObj m c v μ s) (Icc 0 (τ * s / c)) := by
        show ContinuousOn (fun Q => (m - s) * (v / m * ES μ Q) - c * Q) _
        exact (continuousOn_const.mul (continuousOn_const.mul
          ((ES_contOn h).mono Icc_subset_Ici_self))).sub (continuousOn_const.mul continuousOn_id)
      obtain ⟨Q, hQ, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hb) hcont
      exact ⟨Q, fun _ _ _ => ⟨hQ, hmax⟩⟩
    · exact ⟨0, fun hτ hs _ => absurd (div_nonneg (mul_nonneg hτ hs) h.cost_pos.le) hb⟩
  choose Qr hQr using hex
  exact ⟨Qr, fun τ s hτ hs hsm => hQr τ s hτ hs hsm⟩

lemma exists_star (h : Standing m c v z μ f f') (hv : 2 * c < v) :
    ∃ Q : ℝ, 0 < Q ∧ (v - 2 * c) / v < cdf μ Q ∧ cdf μ Q < (v - 2 * c) / (v - c) ∧
      v * (m - m * c / (v * (1 - cdf μ Q))) / (c * m) * ES μ Q = Q := by
  have hc := h.cost_pos
  have hm := h.tokens_pos
  have hv0 : 0 < v := by linarith
  have hvc : 0 < v - c := by linarith
  have hv2 : 0 < v - 2 * c := by linarith
  set a0 := (v - 2 * c) / v with ha0d
  set b0 := (v - 2 * c) / (v - c) with hb0d
  have ha0 : 0 < a0 := div_pos hv2 hv0
  have hab : a0 < b0 := div_lt_div_of_pos_left hv2 hvc (by linarith)
  have hb1 : b0 < 1 := (div_lt_one hvc).2 (by linarith)
  obtain ⟨hqa0, hFqa⟩ := Finv_spec h ha0 (hab.trans hb1)
  obtain ⟨hqb0, hFqb⟩ := Finv_spec h (ha0.trans hab) hb1
  set qa := Finv μ a0
  set qb := Finv μ b0
  have hqab : qa < qb := F_lt_rev (by rw [hFqa, hFqb]; exact hab)
  set H : ℝ → ℝ := fun Q => v * (m - m * c / (v * (1 - cdf μ Q))) / (c * m) * ES μ Q - Q
    with hHd
  have hden : ∀ Q ∈ Icc qa qb, v * (1 - cdf μ Q) ≠ 0 := by
    intro Q hQ
    have := monotone_cdf μ hQ.2
    rw [hFqb] at this
    exact mul_ne_zero hv0.ne' (by linarith)
  have hFc : ContinuousOn (fun Q => cdf μ Q) (Icc qa qb) := h.cdf_continuous.continuousOn
  have hHc : ContinuousOn H (Icc qa qb) := by
    refine ContinuousOn.sub (ContinuousOn.mul ?_ ?_) continuousOn_id
    · refine ContinuousOn.div_const ?_ _
      refine continuousOn_const.mul (continuousOn_const.sub ?_)
      exact continuousOn_const.div (continuousOn_const.mul (continuousOn_const.sub hFc)) hden
    · exact (ES_contOn h).mono (fun Q hQ => mem_Ici.2 (hqa0.le.trans hQ.1))
  have hHa : 0 < H qa := by
    have e1 : 1 - cdf μ qa = 2 * c / v := by
      rw [hFqa, ha0d]; field_simp; ring
    have hg := ES_gt h hqa0 (by rw [hFqa]; exact hab.trans hb1)
    rw [e1] at hg
    simp only [hHd]
    rw [e1]
    have e2 : v * (m - m * c / (v * (2 * c / v))) / (c * m) = v / (2 * c) := by
      field_simp; ring
    rw [e2]
    have e3 : qa * (2 * c / v) * (v / (2 * c)) = qa := by field_simp
    have e4 : qa * (2 * c / v) * (v / (2 * c)) < ES μ qa * (v / (2 * c)) :=
      mul_lt_mul_of_pos_right hg (by positivity)
    linarith
  have hHb : H qb < 0 := by
    have e1 : 1 - cdf μ qb = c / (v - c) := by
      rw [hFqb, hb0d]; field_simp; ring
    simp only [hHd]
    rw [e1]
    have e2 : v * (m - m * c / (v * (c / (v - c)))) / (c * m) = 1 := by
      field_simp; ring
    rw [e2]
    linarith [ES_lt h hqb0]
  obtain ⟨Q, hQ, hHQ⟩ := intermediate_value_Icc' hqab.le hHc ⟨hHb.le, hHa.le⟩
  have hQa : qa < Q := by
    rcases hQ.1.eq_or_lt with he | hl
    · rw [← he] at hHQ; linarith
    · exact hl
  have hQb : Q < qb := by
    rcases hQ.2.eq_or_lt with he | hl
    · rw [he] at hHQ; linarith
    · exact hl
  refine ⟨Q, hqa0.trans hQa, ?_, ?_, ?_⟩
  · rw [← hFqa]; exact F_strict h hqa0.le hQa (by rw [hFqa]; exact hab.trans hb1)
  · rw [← hFqb]
    exact F_strict h (hqa0.trans hQa).le hQb
      (lt_of_le_of_lt (monotone_cdf μ hQb.le) (by rw [hFqb]; exact hb1))
  · simp only [hHd] at hHQ; linarith

section Star

variable {Qr : ℝ → ℝ → ℝ} {Qs ns : ℝ}

lemma K1 (h : Standing m c v z μ f f') (hQr : ProdOptimal m c v μ Qr)
    (hQs : 0 < Qs) (hF1 : cdf μ Qs < 1) (hns0 : 0 < ns) (hnsm : ns < m)
    (hcross : v * ns / (c * m) * ES μ Qs = Qs)
    (hcond : (m - ns) * (v / m) * (1 - cdf μ Qs) = c) :
    Qr (v / m * ES μ Qs) ns = Qs := by
  have hc := h.cost_pos
  have hm := h.tokens_pos
  have hv0 : 0 < v := by linarith [h.value_gt_cost]
  have hτ : 0 ≤ v / m * ES μ Qs := by have := ES_nonneg h hQs.le; positivity
  have hB : v / m * ES μ Qs * ns / c = Qs := by
    rw [show v / m * ES μ Qs * ns / c = v * ns / (c * m) * ES μ Qs by field_simp]
    exact hcross
  have hmem := (hQr _ ns hτ hns0.le hnsm.le).1
  rw [hB] at hmem
  apply le_antisymm hmem.2
  exact maxQ_ge h hQr hτ hns0.le hnsm hQs hB.ge hF1 hcond.ge

lemma Kw (h : Standing m c v z μ f f') (hQr : ProdOptimal m c v μ Qr)
    (hQs : 0 < Qs) (hF1 : cdf μ Qs < 1) (hns0 : 0 < ns) (hnsm : ns < m)
    (hcross : v * ns / (c * m) * ES μ Qs = Qs)
    (hcond : (m - ns) * (v / m) * (1 - cdf μ Qs) = c) :
    sstar m v z μ Qr (v / m * ES μ Qs) ns = ns ∧
    wealth m c v z μ Qr (v / m * ES μ Qs) ns = v * ES μ Qs - c * Qs := by
  have hm := h.tokens_pos
  have hK := K1 h hQr hQs hF1 hns0 hnsm hcross hcond
  have hss : sstar m v z μ Qr (v / m * ES μ Qs) ns = ns := by
    unfold sstar u margin
    rw [hK, if_pos (by simp)]
  refine ⟨hss, ?_⟩
  simp only [wealth]
  rw [hss, hK]
  field_simp
  ring

lemma K5 (h : Standing m c v z μ f f') (hQr : ProdOptimal m c v μ Qr)
    (hQs : 0 < Qs) (hF1 : cdf μ Qs < 1) (hns0 : 0 < ns) (hnsm : ns < m)
    (hcross : v * ns / (c * m) * ES μ Qs = Qs)
    (hcond : (m - ns) * (v / m) * (1 - cdf μ Qs) = c)
    (hG : c ≤ v * (1 - cdf μ Qs))
    {τ n : ℝ} (hτ : 0 ≤ τ) (hn : 0 ≤ n) (hnm : n ≤ m) :
    wealth m c v z μ Qr τ n ≤ v * ES μ Qs - c * Qs ∧
    (v * ES μ Qs - c * Qs ≤ wealth m c v z μ Qr τ n →
      τ = v / m * ES μ Qs ∧ n = ns) := by
  have hc := h.cost_pos
  have hm := h.tokens_pos
  have hz : 0 < z := lt_of_lt_of_le hm h.pool_ge_tokens
  have hv0 : 0 < v := by linarith [h.value_gt_cost]
  have hESs := ES_gt h hQs hF1
  have hW : 0 < v * ES μ Qs - c * Qs := by
    have := G_inc h (a := v) (Q := 0) (Q' := Qs) (Q0 := Qs) hv0 le_rfl hQs le_rfl hF1 hG
    rw [ES_zero h] at this; linarith
  simp only [wealth, sstar]
  split_ifs with hu
  · -- full participation
    obtain ⟨hmem, -⟩ := hQr τ n hτ hn hnm
    rcases hn.eq_or_lt with hn0 | hn0
    · subst hn0
      have hQ0 : Qr τ 0 = 0 := by
        have := hmem.2; simp at this; linarith [hmem.1]
      rw [hQ0, ES_zero h]
      constructor
      · simp; linarith
      · intro hh; simp at hh; linarith
    have hmaxQ : ∀ x : ℝ, 0 ≤ x → x ≤ τ * n / c →
        (m - n) * (v / m) * (1 - cdf μ x) ≤ c → Qr τ n ≤ x :=
      fun x hx hxB hxc => maxQ_le h hQr hτ hn hnm hx hxB hxc
    unfold u margin at hu
    generalize hQd : Qr τ n = Q at hmem hu hmaxQ ⊢
    have hmarg : τ ≤ v / m * ES μ Q := by
      have hnz : 0 < n / z := div_pos hn0 hz
      by_contra hh; push_neg at hh
      have : n / z * (v / m * ES μ Q - τ) < 0 := mul_neg_of_pos_of_neg hnz (by linarith)
      linarith
    have hESQ := ES_nonneg h hmem.1
    have hQle : Q ≤ Qs := by
      by_contra hlt; push_neg at hlt
      rcases le_or_gt n ns with hnn | hnn
      · have hr := ES_ratio h hQs hlt hF1
        have h1 : τ * n ≤ v / m * ES μ Q * ns :=
          mul_le_mul hmarg hnn hn (mul_nonneg (div_nonneg hv0.le hm.le) hESQ)
        have h2 : Q ≤ v * ns / (c * m) * ES μ Q := by
          have : Q ≤ τ * n / c := hmem.2
          have e : v * ns / (c * m) * ES μ Q = v / m * ES μ Q * ns / c := by
            field_simp
          rw [e]
          exact this.trans (div_le_div_of_nonneg_right h1 hc.le)
        have h3 := mul_le_mul_of_nonneg_right h2 (ES_nonneg h hQs.le)
        have h4 : v * ns / (c * m) * ES μ Q * ES μ Qs = ES μ Q * Qs := by
          rw [show v * ns / (c * m) * ES μ Q * ES μ Qs = ES μ Q * (v * ns / (c * m) * ES μ Qs)
            by ring, hcross]
        nlinarith
      · have hQsB : Qs ≤ τ * n / c := hlt.le.trans hmem.2
        have hcond' : (m - n) * (v / m) * (1 - cdf μ Qs) ≤ c := by
          rw [← hcond]
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
        have := hmaxQ Qs hQs.le hQsB hcond'
        linarith
    have hwle : τ * n - c * Q + (m - n) * (v / m * ES μ Q) ≤ v * ES μ Q - c * Q := by
      have e : v / m * ES μ Q * n + (m - n) * (v / m * ES μ Q) = v * ES μ Q := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_right hmarg hn
      linarith
    have hGle : v * ES μ Q - c * Q ≤ v * ES μ Qs - c * Qs := by
      rcases hQle.eq_or_lt with he | hl
      · rw [he]
      · exact (G_inc h hv0 hmem.1 hl le_rfl hF1 hG).le
    refine ⟨hwle.trans hGle, fun hge => ?_⟩
    have hQeq : Q = Qs := by
      rcases hQle.eq_or_lt with he | hl
      · exact he
      · have := G_inc h hv0 hmem.1 hl le_rfl hF1 hG; linarith
    rw [hQeq] at hwle hmarg hmem
    have hτeq : τ = v / m * ES μ Qs := by
      refine le_antisymm hmarg ?_
      have e : v / m * ES μ Qs * n + (m - n) * (v / m * ES μ Qs) = v * ES μ Qs := by
        field_simp; ring
      rw [hQeq] at hge
      by_contra hh; push_neg at hh
      have := mul_lt_mul_of_pos_right hh hn0
      linarith
    refine ⟨hτeq, ?_⟩
    have hτpos : 0 < v / m * ES μ Qs := by
      have : 0 < ES μ Qs := lt_of_le_of_lt (mul_nonneg hQs.le (by linarith)) hESs
      positivity
    rcases lt_trichotomy n ns with hl | he | hl
    · exfalso
      have h1 := hmem.2
      rw [hτeq] at h1
      have h2 : v / m * ES μ Qs * n / c < v / m * ES μ Qs * ns / c :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hl hτpos) hc
      have h3 : v / m * ES μ Qs * ns / c = Qs := by
        rw [show v / m * ES μ Qs * ns / c = v * ns / (c * m) * ES μ Qs by field_simp]
        exact hcross
      linarith
    · exact he
    · exfalso
      have hgs : (m - n) * (v / m) * (1 - cdf μ Qs) < c := by
        rw [← hcond]
        apply mul_lt_mul_of_pos_right _ (by linarith)
        apply mul_lt_mul_of_pos_right _ (by positivity)
        linarith
      have hcont : ContinuousAt (fun x => (m - n) * (v / m) * (1 - cdf μ x)) Qs :=
        (continuous_const.mul (continuous_const.sub h.cdf_continuous)).continuousAt
      have hev := hcont.eventually (gt_mem_nhds hgs)
      obtain ⟨x, hx, hxI⟩ :=
        ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT hQs)).exists
      have hxB : x ≤ τ * n / c := hxI.2.le.trans hmem.2
      have := hmaxQ x hxI.1.le hxB hx.le
      rw [hQeq] at this
      linarith [hxI.2]
  · -- no participation
    have hmem := (hQr τ 0 hτ le_rfl hm.le).1
    have hQ0 : Qr τ 0 = 0 := by simpa using hmem
    rw [hQ0, ES_zero h]
    constructor
    · simp; linarith
    · intro hh; simp at hh; linarith

end Star

end TokenICO.UtilityEq.P3Aux

open TokenICO.UtilityEq TokenICO.UtilityEq.P3Aux Set

theorem solution (m c v z : ℝ) (μ : Measure ℝ) (f f' : ℝ → ℝ)
    (h : Standing m c v z μ f f')
    (ht : TechCond c v μ f f') :
    (v ≤ 2 * c →
      ∀ Qr : ℝ → ℝ → ℝ, ProdOptimal m c v μ Qr →
        ∀ τ n : ℝ, 0 ≤ τ → 0 ≤ n → n ≤ m →
          τ * sstar m v z μ Qr τ n = 0) ∧
    (2 * c < v →
      ∃ τs ns : ℝ,
        (∃ Qr : ℝ → ℝ → ℝ, IsEquilibrium m c v z μ Qr τs ns) ∧
        (∀ Qr : ℝ → ℝ → ℝ, ∀ τ n : ℝ,
          IsEquilibrium m c v z μ Qr τ n → τ = τs ∧ n = ns) ∧
        ns ∈ Set.Ioo (m * c / v) (m / 2) ∧
        v * ns / (c * m) * ES μ (Qcap m c v μ ns) = Qcap m c v μ ns ∧
        (∀ n ∈ Set.Ioo (m * c / v) (m / 2),
          v * n / (c * m) * ES μ (Qcap m c v μ n) = Qcap m c v μ n →
            n = ns) ∧
        τs = v / m * ES μ (Qcap m c v μ ns) ∧
        (∀ Qr : ℝ → ℝ → ℝ,
          IsEquilibrium m c v z μ Qr τs ns →
            Qr τs (sstar m v z μ Qr τs ns) = Qcap m c v μ ns ∧
            sstar m v z μ Qr τs ns = ns ∧
            c * Qr τs (sstar m v z μ Qr τs ns) =
              τs * sstar m v z μ Qr τs ns) ∧
        (∫ x, v / m * min (Qcap m c v μ ns) x ∂μ) = τs) := by
  have hc := h.cost_pos
  have hm := h.tokens_pos
  have hv0 : 0 < v := by linarith [h.value_gt_cost]
  have hz : 0 < z := lt_of_lt_of_le hm h.pool_ge_tokens
  refine ⟨?_, ?_⟩
  · -- (i) failure when v ≤ 2c
    intro hv Qr hQr τ n hτ hn hnm
    rcases hτ.eq_or_lt with hτ0 | hτ0
    · rw [← hτ0, zero_mul]
    rcases hn.eq_or_lt with hn0 | hn0
    · subst hn0; unfold sstar; split_ifs <;> simp
    have hs : sstar m v z μ Qr τ n = 0 := by
      unfold sstar
      rw [if_neg]
      intro hu
      unfold u margin at hu
      obtain ⟨hmem, -⟩ := hQr τ n hτ hn hnm
      have hmarg : τ ≤ v / m * ES μ (Qr τ n) := by
        have hnz : 0 < n / z := div_pos hn0 hz
        by_contra hh; push_neg at hh
        have : n / z * (v / m * ES μ (Qr τ n) - τ) < 0 :=
          mul_neg_of_pos_of_neg hnz (by linarith)
        linarith
      rcases lt_or_ge n (m * c / v) with hlt | hge
      · have h1 := ES_le h hmem.1
        have h2 := hmem.2
        have h3 : v / m * ES μ (Qr τ n) ≤ v / m * (τ * n / c) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        have h4 : v / m * (τ * n / c) < τ := by
          have : v * n < m * c := by rwa [lt_div_iff₀ hv0, mul_comm n v] at hlt
          rw [show v / m * (τ * n / c) = τ * (v * n) / (m * c) by field_simp]
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      · have hcond : (m - n) * (v / m) * (1 - cdf μ 0) ≤ c := by
          rw [h.cdf_nonpositive 0 le_rfl, sub_zero, mul_one]
          have : m * c / v ≤ n := hge
          rw [div_le_iff₀ hv0] at this
          rw [show (m - n) * (v / m) = (m - n) * v / m by ring, div_le_iff₀ hm]
          nlinarith
        have := maxQ_le h hQr hτ hn hnm le_rfl (by positivity) hcond
        have hQ0 : Qr τ n = 0 := le_antisymm this hmem.1
        rw [hQ0, ES_zero h] at hmarg
        linarith
    rw [hs, mul_zero]
  · -- (ii) the unique equilibrium
    intro hv
    obtain ⟨Qs, hQs, hFa, hFb, hcrossN⟩ := exists_star h hv
    have hvc : 0 < v - c := by linarith
    have hv2 : 0 < v - 2 * c := by linarith
    set y := cdf μ Qs with hyd
    have hb1 : (v - 2 * c) / (v - c) < 1 := (div_lt_one hvc).2 (by linarith)
    have hF1 : y < 1 := hFb.trans hb1
    have hw : 0 < 1 - y := by linarith
    have hwlo : c / (v - c) < 1 - y := by
      have : 1 - (v - 2 * c) / (v - c) = c / (v - c) := by field_simp; ring
      linarith
    have hwhi : 1 - y < 2 * c / v := by
      have : 1 - (v - 2 * c) / v = 2 * c / v := by field_simp; ring
      linarith
    set ns := m - m * c / (v * (1 - y)) with hnsd
    have hmns : m - ns = m * c / (v * (1 - y)) := by rw [hnsd]; ring
    have hns_lo : m * c / v < ns := by
      have : m * c / (v * (1 - y)) < m - m * c / v := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hvc] at hwlo
        have e : (m - m * c / v) * (v * (1 - y)) = m * ((v - c) * (1 - y)) := by
          field_simp
        rw [e]
        nlinarith
      linarith
    have hns_hi : ns < m / 2 := by
      have : m / 2 < m * c / (v * (1 - y)) := by
        rw [lt_div_iff₀ (by positivity)]
        rw [lt_div_iff₀ hv0] at hwhi
        nlinarith
      linarith
    have hns0 : 0 < ns := lt_of_le_of_lt (by positivity) hns_lo
    have hnsm : ns < m := by linarith
    have hyeq : 1 - m / (m - ns) * (c / v) = y := by
      rw [hmns]; field_simp; ring
    have hQcap : Qcap m c v μ ns = Qs := by
      unfold Qcap; rw [hyeq]; exact Finv_F h hQs hF1
    have hcond : (m - ns) * (v / m) * (1 - y) = c := by
      rw [hmns]; field_simp
    have hG : c ≤ v * (1 - y) := by
      have : c / (v - c) * v ≥ c := by
        rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hvc]; nlinarith
      nlinarith
    have hcross : v * ns / (c * m) * ES μ Qs = Qs := hcrossN
    have hESpos : 0 < ES μ Qs :=
      lt_of_le_of_lt (mul_nonneg hQs.le hw.le) (ES_gt h hQs hF1)
    refine ⟨v / m * ES μ Qs, ns, ?_, ?_, ⟨hns_lo, hns_hi⟩, ?_, ?_, ?_, ?_, ?_⟩
    · -- existence
      obtain ⟨Qr, hQr⟩ := exists_prodOptimal h
      refine ⟨Qr, hQr, by positivity, hns0.le, hnsm.le, fun τ' n' hτ' hn' hnm' => ?_⟩
      have h1 := (K5 h hQr hQs hF1 hns0 hnsm hcross hcond hG hτ' hn' hnm').1
      have h2 := (Kw h hQr hQs hF1 hns0 hnsm hcross hcond).2
      linarith
    · -- uniqueness
      rintro Qr τ n ⟨hQr, hτ, hn, hnm, hmax⟩
      have h1 := hmax (v / m * ES μ Qs) ns (by positivity) hns0.le hnsm.le
      have h2 := (Kw h hQr hQs hF1 hns0 hnsm hcross hcond).2
      rw [h2] at h1
      exact (K5 h hQr hQs hF1 hns0 hnsm hcross hcond hG hτ hn hnm).2 h1
    · rw [hQcap]; exact hcross
    · -- uniqueness of the crossing
      intro n hn heq
      have hn0 : 0 < n := lt_of_le_of_lt (by positivity) hn.1
      have hnm : n < m := by linarith [hn.2]
      set yn := 1 - m / (m - n) * (c / v) with hynd
      have hmn : 0 < m - n := by linarith
      have hyn1 : yn < 1 := by
        have : 0 < m / (m - n) * (c / v) := by positivity
        linarith
      have hyn0 : 0 < yn := by
        have h2 : m / (m - n) < 2 := by
          rw [div_lt_iff₀ hmn]; linarith [hn.2]
        have h3 : m / (m - n) * (c / v) < 2 * (c / v) :=
          mul_lt_mul_of_pos_right h2 (by positivity)
        have h4 : 2 * (c / v) < 1 := by
          rw [show 2 * (c / v) = 2 * c / v by ring, div_lt_one hv0]; linarith
        linarith
      obtain ⟨hQn0, hFQn⟩ := Finv_spec h hyn0 hyn1
      have hQcn : Qcap m c v μ n = Finv μ yn := rfl
      rw [hQcn] at heq
      set Qn := Finv μ yn
      have hESn : 0 < ES μ Qn :=
        lt_of_le_of_lt (mul_nonneg hQn0.le (by rw [hFQn]; linarith))
          (ES_gt h hQn0 (by rw [hFQn]; exact hyn1))
      have hy' : y = 1 - m / (m - ns) * (c / v) := hyeq.symm
      rcases lt_trichotomy n ns with hl | he | hl
      · exfalso
        have hyy : y < yn := by
          rw [hy', hynd]
          have : m / (m - n) < m / (m - ns) :=
            div_lt_div_of_pos_left hm (by linarith) (by linarith)
          have := mul_lt_mul_of_pos_right this (show 0 < c / v by positivity)
          linarith
        have hQQ : Qs < Qn := F_lt_rev (by rw [hFQn]; exact hyy)
        have hr := ES_ratio h hQs hQQ hF1
        have e : (v * ns / (c * m) - v * n / (c * m)) * (ES μ Qs * ES μ Qn) =
            Qs * ES μ Qn - Qn * ES μ Qs := by
          linear_combination (ES μ Qn) * hcross - (ES μ Qs) * heq
        have hP := mul_pos hESpos hESn
        have hk : v * ns / (c * m) - v * n / (c * m) < 0 := by
          by_contra hh; push_neg at hh
          have := mul_nonneg hh hP.le
          linarith
        have e2 : v * ns / (c * m) - v * n / (c * m) = v / (c * m) * (ns - n) := by ring
        have : 0 < v / (c * m) * (ns - n) := mul_pos (by positivity) (by linarith)
        linarith
      · exact he
      · exfalso
        have hyy : yn < y := by
          rw [hy', hynd]
          have : m / (m - ns) < m / (m - n) :=
            div_lt_div_of_pos_left hm hmn (by linarith)
          have := mul_lt_mul_of_pos_right this (show 0 < c / v by positivity)
          linarith
        have hQQ : Qn < Qs := F_lt_rev (by rw [hFQn]; exact hyy)
        have hr := ES_ratio h hQn0 hQQ (by rw [hFQn]; exact hyn1)
        have e : (v * n / (c * m) - v * ns / (c * m)) * (ES μ Qs * ES μ Qn) =
            Qn * ES μ Qs - Qs * ES μ Qn := by
          linear_combination (ES μ Qs) * heq - (ES μ Qn) * hcross
        have hP := mul_pos hESpos hESn
        have hk : v * n / (c * m) - v * ns / (c * m) < 0 := by
          by_contra hh; push_neg at hh
          have := mul_nonneg hh hP.le
          linarith
        have e2 : v * n / (c * m) - v * ns / (c * m) = v / (c * m) * (n - ns) := by ring
        have : 0 < v / (c * m) * (n - ns) := mul_pos (by positivity) (by linarith)
        linarith
    · rw [hQcap]
    · intro Qr hEq
      have hQr := hEq.1
      obtain ⟨hss, -⟩ := Kw h hQr hQs hF1 hns0 hnsm hcross hcond
      have hK := K1 h hQr hQs hF1 hns0 hnsm hcross hcond
      rw [hss, hK, hQcap]
      refine ⟨rfl, rfl, ?_⟩
      have : v / m * ES μ Qs * ns = c * (v * ns / (c * m) * ES μ Qs) := by
        field_simp
      rw [this, hcross]
    · rw [hQcap]
      simp_rw [min_comm Qs]
      rw [integral_const_mul]
      rfl
