-- Prove2me | solution 1 for XuMannorRobust.Quantile.theorem5_quantile_truncated_mean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:09:43.55454+00:00
-- url     : https://prove2.me/submissions/177032d7-551b-44de-9e4b-cbb90283b02d

import Definitions.Def_XuMannorRobust_Quantile_IsPseudoRobust
import Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_XuMannorRobust_Quantile_LossQuantile
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi



open MeasureTheory Filter Set

namespace XuQuantileHelpers

theorem support_nonneg (P : Measure ℝ) (hP : P (Iio 0) = 0) :
    ∀ᵐ x ∂P, 0 ≤ x := by
  rw [ae_iff]
  simpa [Set.Iio] using hP

theorem integrable_min (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Iio 0) = 0) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => min x t) P := by
  apply (integrable_const t).mono'
    ((continuous_id.min continuous_const).aestronglyMeasurable)
  filter_upwards [support_nonneg P hP] with x hx
  simp only [id_eq]
  rw [Real.norm_eq_abs,abs_of_nonneg (le_min hx ht)]
  exact min_le_right _ _

theorem min_supporting_line (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Iio 0) = 0) (q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hleft : ∀ x ∈ S, x ≤ q) (hright : ∀ x ∉ S, q ≤ x) :
    (∫ x, min x t ∂P) ≤ (∫ x, min x q ∂P) + (1-P.real S)*(t-q) := by
  have hI : Integrable (Sᶜ.indicator (fun _ : ℝ => t-q)) P :=
    (integrable_const (t-q)).indicator hS.compl
  have hp : ∀ x : ℝ, min x t ≤ min x q + Sᶜ.indicator (fun _ => t-q) x := by
    intro x
    by_cases hx : x ∈ S
    · simpa [hx,min_eq_left (hleft x hx)] using (min_le_left x t)
    · simpa [hx,min_eq_right (hright x hx)] using (min_le_right x t)
  have hi := integral_mono_ae (integrable_min P hP t ht)
    ((integrable_min P hP q hq).add hI) (Eventually.of_forall hp)
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_min P hP q hq) hI,
    integral_indicator_const _ hS.compl,smul_eq_mul,probReal_compl_eq_one_sub hS] at hi
  exact hi

theorem quantile_maximizes (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Iio 0) = 0) (beta q : ℝ) (hq : 0 ≤ q)
    (hlo : P.real (Iio q) ≤ beta) (hhi : beta ≤ P.real (Iic q)) :
    ∀ t : ℝ, 0 ≤ t →
      (∫ x, min x t ∂P) - (1-beta)*t ≤
        (∫ x, min x q ∂P) - (1-beta)*q := by
  intro t ht
  rcases le_total t q with h | h
  · have hb := min_supporting_line P hP q t hq ht (Iio q) measurableSet_Iio
      (fun x hx => hx.le) (fun x hx => le_of_not_gt hx)
    have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlo) (sub_nonpos.mpr h)
    nlinarith
  · have hb := min_supporting_line P hP q t hq ht (Iic q) measurableSet_Iic
      (fun x hx => hx) (fun x hx => (lt_of_not_ge hx).le)
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hhi) (sub_nonneg.mpr h)
    nlinarith

theorem quantile_value_formula (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Iio 0) = 0) (beta q : ℝ) (hq : 0 ≤ q) :
    (∫ x, min x q ∂P) - (1-beta)*q =
      (∫ x in Iio q, x ∂P) + (beta-P.real (Iio q))*q := by
  have hs : (∫ x, min x q ∂P) =
      (∫ x in Iio q, x ∂P) + P.real (Iio q)ᶜ*q := by
    rw [← integral_add_compl measurableSet_Iio (integrable_min P hP q hq)]
    rw [setIntegral_congr_fun measurableSet_Iio (fun x hx => min_eq_left hx.le)]
    rw [setIntegral_congr_fun measurableSet_Iio.compl
      (fun x hx => min_eq_right (le_of_not_gt hx))]
    rw [setIntegral_const,smul_eq_mul]
  rw [hs,probReal_compl_eq_one_sub measurableSet_Iio]
  ring

theorem quantile_noatom_adjustment (P : Measure ℝ) [IsProbabilityMeasure P]
    (beta q : ℝ) (hlo : P.real (Iio q) ≤ beta) (hhi : beta ≤ P.real (Iic q))
    (hno : P {q} = 0) : beta = P.real (Iio q) := by
  have hset : Iic q = Iio q ∪ {q} := by
    ext x
    simp [le_iff_lt_or_eq]
  have hm : P (Iic q) = P (Iio q) := by
    rw [hset,measure_union (by
      rw [Set.disjoint_left]
      intro x hx hxq
      have hxeq : x = q := hxq
      subst x
      exact lt_irrefl q hx) (measurableSet_singleton q),hno,add_zero]
  have hmr : P.real (Iic q) = P.real (Iio q) := congrArg ENNReal.toReal hm
  linarith

end XuQuantileHelpers


open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open XuMannorRobust.Quantile

namespace XuProof
variable (P : Measure ℝ) [IsProbabilityMeasure P]

theorem q_zero : quantileValue P 0 = 0 := by
  have hs : {c : ℝ | 0 ≤ (P (Iic c)).toReal} = univ := by ext; simp
  simp [quantileValue,hs]

theorem cdf_negative (hP : P (Iio 0) = 0) (x : ℝ) (hx : x < 0) : cdf P x = 0 := by
  rw [cdf_eq_real,measureReal_def]
  have hz : P (Iic x) = 0 := measure_mono_null (fun y hy => lt_of_le_of_lt hy hx) hP
  simp [hz]

theorem qset_nonempty (β : ℝ) (hβ : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) :
    {c : ℝ | β ≤ (P (Iic c)).toReal}.Nonempty := by
  rcases hfin with hlt|⟨M,hM⟩
  · obtain ⟨x,hx⟩ := ((tendsto_cdf_atTop P).eventually (eventually_gt_nhds hlt)).exists
    exact ⟨x,le_of_lt (by simpa [cdf_eq_real,measureReal_def] using hx)⟩
  · exact ⟨M,by simpa [hM] using hβ⟩

theorem qset_bdd (hP : P (Iio 0) = 0) (β : ℝ) (hβ : 0 < β) :
    BddBelow {c : ℝ | β ≤ (P (Iic c)).toReal} := by
  refine ⟨0,?_⟩
  intro c hc
  by_contra hh
  have hz := cdf_negative P hP c (lt_of_not_ge hh)
  rw [cdf_eq_real,measureReal_def] at hz
  change β ≤ (P (Iic c)).toReal at hc
  rw [hz] at hc
  linarith

theorem q_nonneg (hP : P (Iio 0) = 0) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) : 0 ≤ quantileValue P β := by
  rcases hβ0.eq_or_lt with rfl|hp
  · rw [q_zero]
  · apply le_csInf (qset_nonempty P β hβ1 hfin)
    intro c hc
    by_contra hh
    have hz := cdf_negative P hP c (lt_of_not_ge hh)
    rw [cdf_eq_real,measureReal_def] at hz
    change β ≤ (P (Iic c)).toReal at hc
    rw [hz] at hc
    linarith

theorem below_q (hP : P (Iio 0) = 0) (β : ℝ) (hβ : 0 < β)
    (x : ℝ) (hx : x < quantileValue P β) : cdf P x < β := by
  by_contra hh
  have hm : x ∈ {c : ℝ | β ≤ (P (Iic c)).toReal} := by
    simpa [cdf_eq_real,measureReal_def] using le_of_not_gt hh
  exact (not_le_of_gt hx) (csInf_le (qset_bdd P hP β hβ) hm)

theorem above_q (β : ℝ) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1)
    (x : ℝ) (hx : quantileValue P β < x) : β ≤ cdf P x := by
  obtain ⟨y,hy,hyx⟩ := exists_lt_of_csInf_lt (qset_nonempty P β hβ1 hfin) hx
  have h : β ≤ cdf P y := by simpa [cdf_eq_real,measureReal_def] using hy
  exact h.trans ((monotone_cdf P) hyx.le)

theorem q_upper (β : ℝ) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) :
    β ≤ P.real (Iic (quantileValue P β)) := by
  rw [← cdf_eq_real]
  apply ge_of_tendsto (((cdf P).right_continuous (quantileValue P β)).mono Ioi_subset_Ici_self)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact above_q P β hβ1 hfin x hx

theorem q_lower (hP : P (Iio 0) = 0) (β : ℝ) (hβ0 : 0 ≤ β) :
    P.real (Iio (quantileValue P β)) ≤ β := by
  rcases hβ0.eq_or_lt with rfl|hp
  · simp [q_zero,measureReal_def,hP]
  · have hleft : Function.leftLim (cdf P) (quantileValue P β) ≤ β := by
      apply le_of_tendsto ((monotone_cdf P).tendsto_leftLim _)
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (below_q P hP β hp x hx).le
    have hnon : 0 ≤ Function.leftLim (cdf P) (quantileValue P β) := by
      exact ge_of_tendsto ((monotone_cdf P).tendsto_leftLim _) (Eventually.of_forall (cdf_nonneg P))
    have he : P (Iio (quantileValue P β)) = ENNReal.ofReal (Function.leftLim (cdf P) (quantileValue P β)) := by
      calc
        _ = (cdf P).measure (Iio (quantileValue P β)) := congrArg (fun μ : Measure ℝ => μ (Iio (quantileValue P β))) (measure_cdf P).symm
        _ = _ := by rw [(cdf P).measure_Iio (tendsto_cdf_atBot P),sub_zero]
    rw [measureReal_def,he,ENNReal.toReal_ofReal hnon]
    exact hleft

theorem q_mono (hP : P (Iio 0) = 0) (β₁ β₂ : ℝ) (hβ₂ : 0 ≤ β₂) (h21 : β₂ ≤ β₁) (hβ₁ : β₁ ≤ 1)
    (hfin : β₁ < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) :
    quantileValue P β₂ ≤ quantileValue P β₁ := by
  rcases hβ₂.eq_or_lt with rfl|hp
  · rw [q_zero]
    exact q_nonneg P hP β₁ h21 hβ₁ hfin
  · apply csInf_le (qset_bdd P hP β₂ hp)
    exact h21.trans (q_upper P β₁ hβ₁ hfin)
end XuProof

namespace XuProof
variable (P P' : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure P']

theorem ae_nonneg (hP : P (Iio 0) = 0) : ∀ᵐ x ∂P, 0 ≤ x := by
  rw [ae_iff]
  simpa [Set.Iio] using hP

theorem min_integrable (hP : P (Iio 0) = 0) (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun x : ℝ => min x q) P := by
  apply (integrable_const q).mono' (by fun_prop)
  filter_upwards [ae_nonneg P hP] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (le_min hx hq)]
  exact min_le_right _ _

theorem min_integral_dom (hP : P (Iio 0) = 0) (hP' : P' (Iio 0) = 0)
    (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (q : ℝ) (hq : 0 ≤ q) :
    (∫ x, min x q ∂P) ≤ ∫ x, min x q ∂P' := by
  have hn : ∀ᵐ x ∂P, 0 ≤ min x q := (ae_nonneg P hP).mono (fun x hx => le_min hx hq)
  have hn' : ∀ᵐ x ∂P', 0 ≤ min x q := (ae_nonneg P' hP').mono (fun x hx => le_min hx hq)
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hn')).mp
  rw [ofReal_integral_eq_lintegral_ofReal (min_integrable P hP q hq) hn,
    ofReal_integral_eq_lintegral_ofReal (min_integrable P' hP' q hq) hn',
    lintegral_eq_lintegral_meas_le P hn (by fun_prop),
    lintegral_eq_lintegral_meas_le P' hn' (by fun_prop)]
  apply lintegral_mono
  intro t
  change P {x : ℝ | t ≤ min x q} ≤ P' {x : ℝ | t ≤ min x q}
  by_cases ht : t ≤ q
  · have he : {x : ℝ | t ≤ min x q} = Ici t := by ext; simp [le_min_iff,ht]
    rw [he]
    exact hdom t
  · have he : {x : ℝ | t ≤ min x q} = ∅ := by ext; simp [le_min_iff,ht]
    rw [he]
    simp

theorem left_mass_dom (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (a : ℝ) :
    P'.real (Iio a) ≤ P.real (Iio a) := by
  have h := ENNReal.toReal_mono (measure_ne_top P' (Ici a)) (hdom a)
  have h1 := probReal_compl_eq_one_sub (μ := P) measurableSet_Ici (s := Ici a)
  have h2 := probReal_compl_eq_one_sub (μ := P') measurableSet_Ici (s := Ici a)
  simp only [compl_Ici] at h1 h2
  change P.real (Ici a) ≤ P'.real (Ici a) at h
  linarith

theorem cdf_dom (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (x : ℝ) :
    cdf P' x ≤ cdf P x := by
  apply ge_of_tendsto (((cdf P).right_continuous x).mono Ioi_subset_Ici_self)
  filter_upwards [self_mem_nhdsWithin] with y hy
  calc
    _ = P'.real (Iic x) := cdf_eq_real P' x
    _ ≤ P'.real (Iio y) := measureReal_mono (Iic_subset_Iio.mpr hy)
    _ ≤ P.real (Iio y) := left_mass_dom P P' hdom y
    _ ≤ P.real (Iic y) := measureReal_mono Iio_subset_Iic_self
    _ = _ := (cdf_eq_real P y).symm

theorem q_dom (hP : P (Iio 0) = 0)
    (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P' (Iic M) = 1) :
    quantileValue P β ≤ quantileValue P' β := by
  rcases hβ0.eq_or_lt with rfl|hp
  · rw [q_zero,q_zero]
  · apply csInf_le (qset_bdd P hP β hp)
    have h := (q_upper P' β hβ1 hfin).trans (by
      simpa [cdf_eq_real] using cdf_dom P P' hdom (quantileValue P' β))
    exact h
end XuProof

namespace XuProof
variable (P : Measure ℝ) [IsProbabilityMeasure P]

theorem truncated_formula (hP : P (Iio 0) = 0) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) :
    truncatedMean P β = (∫ x, min x (quantileValue P β) ∂P) - (1-β)*quantileValue P β := by
  have hq := q_nonneg P hP β hβ0 hβ1 hfin
  have hlo := q_lower P hP β hβ0
  have hhi := q_upper P β hβ1 hfin
  have hf := XuQuantileHelpers.quantile_value_formula P hP β (quantileValue P β) hq
  unfold truncatedMean
  split_ifs with hz
  · have he := XuQuantileHelpers.quantile_noatom_adjustment P β (quantileValue P β) hlo hhi hz
    have hd : β-P.real (Iio (quantileValue P β)) = 0 := sub_eq_zero.mpr he
    rw [hd,zero_mul,add_zero] at hf
    exact hf.symm
  · exact hf.symm

theorem truncated_mono (hP : P (Iio 0) = 0) (β₁ β₂ : ℝ) (hβ₂ : 0 ≤ β₂) (h21 : β₂ ≤ β₁) (hβ₁ : β₁ ≤ 1)
    (hfin : β₁ < 1 ∨ ∃ M : ℝ, P (Iic M) = 1) :
    truncatedMean P β₂ ≤ truncatedMean P β₁ := by
  have hf₂ : β₂ < 1 ∨ ∃ M : ℝ, P (Iic M) = 1 := hfin.elim (fun h => Or.inl (lt_of_le_of_lt h21 h)) Or.inr
  have hq₂ := q_nonneg P hP β₂ hβ₂ (h21.trans hβ₁) hf₂
  have hq₁ := q_nonneg P hP β₁ (hβ₂.trans h21) hβ₁ hfin
  rw [truncated_formula P hP β₂ hβ₂ (h21.trans hβ₁) hf₂,
    truncated_formula P hP β₁ (hβ₂.trans h21) hβ₁ hfin]
  have hmax := XuQuantileHelpers.quantile_maximizes P hP β₁ (quantileValue P β₁) hq₁
    (q_lower P hP β₁ (hβ₂.trans h21)) (q_upper P β₁ hβ₁ hfin) (quantileValue P β₂) hq₂
  nlinarith [mul_nonneg (sub_nonneg.mpr h21) hq₂]

variable (P' : Measure ℝ) [IsProbabilityMeasure P']

theorem fin_of_dom (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (β : ℝ)
    (hfin : β < 1 ∨ ∃ M : ℝ, P' (Iic M) = 1) :
    β < 1 ∨ ∃ M : ℝ, P (Iic M) = 1 := by
  rcases hfin with h|⟨M,hM⟩
  · exact Or.inl h
  · right
    refine ⟨M,?_⟩
    have hc' : cdf P' M = 1 := by simp [cdf_eq_real,measureReal_def,hM]
    have hc : cdf P M = 1 := le_antisymm (cdf_le_one P M) (by rw [← hc']; exact cdf_dom P P' hdom M)
    rw [← ofReal_cdf P M,hc,ENNReal.ofReal_one]

theorem truncated_dom (hP : P (Iio 0) = 0) (hP' : P' (Iio 0) = 0)
    (hdom : ∀ a : ℝ, P (Ici a) ≤ P' (Ici a)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hfin : β < 1 ∨ ∃ M : ℝ, P' (Iic M) = 1) :
    truncatedMean P β ≤ truncatedMean P' β := by
  have hfinP := fin_of_dom P P' hdom β hfin
  have hq := q_nonneg P hP β hβ0 hβ1 hfinP
  have hq' := q_nonneg P' hP' β hβ0 hβ1 hfin
  rw [truncated_formula P hP β hβ0 hβ1 hfinP,truncated_formula P' hP' β hβ0 hβ1 hfin]
  have hm := min_integral_dom P P' hP hP' hdom (quantileValue P β) hq
  have hh := XuQuantileHelpers.quantile_maximizes P' hP' β (quantileValue P' β) hq'
    (q_lower P' hP' β hβ0) (q_upper P' β hβ1 hfin) (quantileValue P β) hq
  linarith
end XuProof
namespace XuPseudoHelpers
open XuMannorRobust.Quantile XuProof

theorem quantile_shift_upper (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0)=0) (hQfin : ∃ M : ℝ,Q (Iic M)=1)
    (beta a e : ℝ) (hbeta : 0 < beta) (hba : beta+a ≤ 1)
    (hcdf : ∀ x : ℝ,Q.real (Iic x) ≤ P.real (Iic (x+e))+a) :
    quantileValue P beta ≤ quantileValue Q (beta+a)+e := by
  apply csInf_le (qset_bdd P hP beta hbeta)
  change beta ≤ P.real (Iic (quantileValue Q (beta+a)+e))
  have hh := q_upper Q (beta+a) hba (Or.inr hQfin)
  have hc := hcdf (quantileValue Q (beta+a))
  linarith

theorem quantile_shift_bounds (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0)=0) (hQ : Q (Iio 0)=0)
    (hPfin : ∃ M : ℝ,P (Iic M)=1) (hQfin : ∃ M : ℝ,Q (Iic M)=1)
    (beta a e : ℝ) (hb0 : 0 < beta) (hb1 : beta < 1) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hlo : 0 ≤ beta-a) (hhi : beta+a ≤ 1)
    (hPQ : ∀ x : ℝ,P.real (Iic x) ≤ Q.real (Iic (x+e))+a)
    (hQP : ∀ x : ℝ,Q.real (Iic x) ≤ P.real (Iic (x+e))+a) :
    quantileValue Q (beta-a)-e ≤ quantileValue P beta ∧
      quantileValue P beta ≤ quantileValue Q (beta+a)+e := by
  refine ⟨?_,quantile_shift_upper P Q hP hQfin beta a e hb0 hhi hQP⟩
  rcases hlo.eq_or_lt with hzero|hpos
  · have harg : beta-a=0 := hzero.symm
    rw [harg,q_zero]
    have hq := q_nonneg P hP beta hb0.le hb1.le (Or.inr hPfin)
    linarith
  · have hh := quantile_shift_upper Q P hQ hPfin (beta-a) a e hpos (by linarith) hPQ
    have hid : beta-a+a=beta := by ring
    rw [hid] at hh
    linarith

theorem truncated_shift_upper (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0)=0) (hQ : Q (Iio 0)=0)
    (hPfin : ∃ M : ℝ,P (Iic M)=1) (hQfin : ∃ M : ℝ,Q (Iic M)=1)
    (beta a e : ℝ) (hb : 0 ≤ beta) (ha : 0 ≤ a) (hba : beta+a ≤ 1)
    (hcap : ∀ t : ℝ,0 ≤ t →
      (∫ x,min x t ∂P) ≤ (∫ x,min x t ∂Q)+e+a*t) :
    truncatedMean P beta ≤ truncatedMean Q (beta+a)+e := by
  have hb1 : beta ≤ 1 := by linarith
  have hba0 : 0 ≤ beta+a := by linarith
  have hq := q_nonneg P hP beta hb hb1 (Or.inr hPfin)
  have hq' := q_nonneg Q hQ (beta+a) hba0 hba (Or.inr hQfin)
  have hmx := XuQuantileHelpers.quantile_maximizes Q hQ (beta+a) (quantileValue Q (beta+a)) hq'
    (q_lower Q hQ (beta+a) hba0) (q_upper Q (beta+a) hba (Or.inr hQfin)) (quantileValue P beta) hq
  have hc := hcap (quantileValue P beta) hq
  rw [truncated_formula P hP beta hb hb1 (Or.inr hPfin),
    truncated_formula Q hQ (beta+a) hba0 hba (Or.inr hQfin)]
  nlinarith

theorem truncated_shift_bounds (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : P (Iio 0)=0) (hQ : Q (Iio 0)=0)
    (hPfin : ∃ M : ℝ,P (Iic M)=1) (hQfin : ∃ M : ℝ,Q (Iic M)=1)
    (beta a e : ℝ) (hb : 0 ≤ beta) (ha : 0 ≤ a)
    (hlo : 0 ≤ beta-a) (hhi : beta+a ≤ 1)
    (hPQ : ∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂P) ≤ (∫ x,min x t ∂Q)+e+a*t)
    (hQP : ∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂Q) ≤ (∫ x,min x t ∂P)+e+a*t) :
    truncatedMean Q (beta-a)-e ≤ truncatedMean P beta ∧
      truncatedMean P beta ≤ truncatedMean Q (beta+a)+e := by
  refine ⟨?_,truncated_shift_upper P Q hP hQ hPfin hQfin beta a e hb ha hhi hPQ⟩
  have hh := truncated_shift_upper Q P hQ hP hQfin hPfin (beta-a) a e hlo ha (by linarith) hQP
  have hid : beta-a+a=beta := by ring
  rw [hid] at hh
  linarith

end XuPseudoHelpers


open Classical MeasureTheory Filter
open scoped BigOperators

noncomputable section

namespace XuPseudoHelpers

private theorem cell_upper {Z ι : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (v : ι → ℝ) (M e : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) (hf : Integrable f μ)
    (hb : ∀ z, 0 ≤ f z ∧ f z ≤ M) (hv : ∀ j, 0 ≤ v j ∧ v j ≤ M)
    (C : Set Z) (hC : MeasurableSet C) (N : Finset ι)
    (hr : ∀ j ∈ N, ∀ z ∈ C, f z ≤ v j+e)
    (n : ℝ) (hn : 0 < n) :
    (∫ z in C, f z ∂μ) ≤ (∑ j ∈ N, v j)/n + e*μ.real C +
      M*|(N.card : ℝ)/n-μ.real C| := by
  classical
  let p := μ.real C
  let B := ∫ z in C, f z ∂μ
  have hp : 0 ≤ p := measureReal_nonneg
  have hBM : B ≤ p*M := by
    have hh := integral_mono (hf.integrableOn : Integrable f (μ.restrict C)) (integrable_const M) (fun z => (hb z).2)
    simpa [B,p,setIntegral_const] using hh
  by_cases hN : N.Nonempty
  · have hc : (0 : ℝ) < N.card := Nat.cast_pos.mpr hN.card_pos
    let m := (∑ j ∈ N, v j)/(N.card : ℝ)
    have hm0 : 0 ≤ m := div_nonneg (Finset.sum_nonneg (fun j _ => (hv j).1)) hc.le
    have hmM : m ≤ M := by
      apply (div_le_iff₀ hc).mpr
      simpa [mul_comm] using (Finset.sum_le_sum (fun j (_ : j ∈ N) => (hv j).2))
    have hzm : ∀ z ∈ C, f z ≤ m+e := by
      intro z hz
      have hh := Finset.sum_le_sum (fun j hj => hr j hj z hz)
      simp only [Finset.sum_const,Finset.sum_add_distrib,nsmul_eq_mul] at hh
      have hm : m*(N.card : ℝ) = ∑ j ∈ N, v j := div_mul_cancel₀ _ hc.ne'
      nlinarith
    have hB : B ≤ p*(m+e) := by
      have hh := integral_mono_ae (hf.integrableOn : Integrable f (μ.restrict C)) (integrable_const (m+e))
        ((ae_restrict_iff' hC).mpr (Eventually.of_forall hzm))
      simpa [B,p,setIntegral_const] using hh
    have hid : (∑ j ∈ N, v j)/n = (N.card : ℝ)/n*m := by
      dsimp [m]
      field_simp
    rw [hid]
    have hbnd : p-(N.card : ℝ)/n ≤ |(N.card : ℝ)/n-p| := by
      simpa only [neg_sub] using neg_le_abs ((N.card : ℝ)/n-p)
    have hm1 := mul_le_mul_of_nonneg_right hbnd hm0
    have hm2 := mul_le_mul_of_nonneg_left hmM (abs_nonneg ((N.card : ℝ)/n-p))
    change B ≤ (N.card : ℝ)/n*m+e*p+M*|(N.card : ℝ)/n-p|
    nlinarith
  · have hNe : N=∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    simp only [hNe,Finset.sum_empty,zero_div,zero_add,Finset.card_empty,Nat.cast_zero,zero_sub,abs_neg]
    rw [abs_of_nonneg (measureReal_nonneg : 0 ≤ μ.real C)]
    change B ≤ e*p+M*p
    nlinarith

theorem partition_upper {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n K : ℕ} (hn : 0 < n) (C : Fin K → Set Z)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (Function.onFun Disjoint C))
    (hcover : (⋃ i,C i)=Set.univ) (s : Fin n → Z) (S : Finset (Fin n))
    (f : Z → ℝ) (v : Fin n → ℝ) (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hf : Integrable f μ) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ M)
    (hr : ∀ j ∈ S, ∀ i, s j ∈ C i → ∀ z ∈ C i, f z ≤ v j+e) :
    (∫ z, f z ∂μ) ≤ (∑ j,v j)/(n : ℝ)+e+
      M*((∑ i,|((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-μ.real (C i)|)+
        ((n : ℝ)-(S.card : ℝ))/(n : ℝ)) := by
  classical
  let N (i : Fin K) := S.filter (fun j => s j ∈ C i)
  let W (i : Fin K) := Finset.univ.filter (fun j => s j ∈ C i)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcover' (z : Z) : ∃ i, z ∈ C i := by
    apply Set.mem_iUnion.mp
    rw [hcover]
    trivial
  have hsum (T : Finset (Fin n)) (g : Fin n → ℝ) :
      ∑ i, ∑ j ∈ T.filter (fun j => s j ∈ C i), g j = ∑ j ∈ T,g j := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨i,hi⟩ := hcover' (s j)
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro k _ hki
      have hk : s j ∉ C k := fun hk => Set.disjoint_left.mp (hdisj hki) hk hi
      simp [hk]
    · simp
  have hNsum : ∑ i,(N i).card = S.card := by
    have hh := hsum S (fun _ => 1)
    simp only [Finset.sum_const, nsmul_eq_mul,mul_one] at hh
    exact_mod_cast hh
  have hWsum : ∑ i,(W i).card = n := by
    have hh := hsum Finset.univ (fun _ => 1)
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ,Fintype.card_fin] at hh
    exact_mod_cast hh
  have hsub (i : Fin K) : N i ⊆ W i := fun j hj =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  have hdev (i : Fin K) : |((N i).card : ℝ)/(n : ℝ)-μ.real (C i)| ≤
      |((W i).card : ℝ)/(n : ℝ)-μ.real (C i)|+
        (((W i).card : ℝ)-((N i).card : ℝ))/(n : ℝ) := by
    have hw : ((N i).card : ℝ)/(n : ℝ) ≤ ((W i).card : ℝ)/(n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card (hsub i)) hnR.le
    calc
      _ ≤ |((N i).card : ℝ)/(n : ℝ)-((W i).card : ℝ)/(n : ℝ)|+
          |((W i).card : ℝ)/(n : ℝ)-μ.real (C i)| := abs_sub_le _ _ _
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hw)]; ring
  have hpop : (∫ z,f z ∂μ) = ∑ i,∫ z in C i,f z ∂μ := by
    simpa only [hcover,setIntegral_univ] using integral_iUnion_fintype hC hdisj (fun i => hf.integrableOn)
  have hmass : ∑ i,μ.real (C i)=1 := by
    have hh := integral_iUnion_fintype (f := fun _ : Z => (1 : ℝ)) hC hdisj
      (fun i => (integrable_const (μ := μ) (1 : ℝ)).integrableOn)
    simpa [hcover,setIntegral_const] using hh.symm
  have hc (i : Fin K) := cell_upper μ f v M e hM he hf hb hv (C i) (hC i) (N i)
    (fun j hj z hz => hr j (Finset.mem_filter.mp hj).1 i (Finset.mem_filter.mp hj).2 z hz)
    (n : ℝ) hnR
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)
  have hdd := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdev i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_div,Finset.sum_sub_distrib] at hh hdd
  rw [← Nat.cast_sum,← Nat.cast_sum,hWsum,hNsum] at hdd
  rw [hpop]
  change _ ≤ (∑ j,v j)/(n : ℝ)+e+M*((∑ i,|((W i).card : ℝ)/(n : ℝ)-μ.real (C i)|)+_)
  have heq : (∑ i, ∑ j ∈ N i,v j) = ∑ j ∈ S,v j := hsum S v
  rw [heq,hmass,mul_one] at hh
  have hvsum : (∑ j ∈ S,v j) ≤ ∑ j,v j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => (hv j).1)
  have hdiv := div_le_div_of_nonneg_right hvsum hnR.le
  have hmul := mul_le_mul_of_nonneg_left hdd hM
  linarith

theorem partition_lower {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n K : ℕ} (hn : 0 < n) (C : Fin K → Set Z)
    (hC : ∀ i, MeasurableSet (C i)) (hdisj : Pairwise (Function.onFun Disjoint C))
    (hcover : (⋃ i,C i)=Set.univ) (s : Fin n → Z) (S : Finset (Fin n))
    (f : Z → ℝ) (v : Fin n → ℝ) (M e : ℝ) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hf : Integrable f μ) (hb : ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hv : ∀ j, 0 ≤ v j ∧ v j ≤ M)
    (hr : ∀ j ∈ S, ∀ i, s j ∈ C i → ∀ z ∈ C i, v j ≤ f z+e) :
    (∑ j,v j)/(n : ℝ) ≤ (∫ z, f z ∂μ)+e+
      M*((∑ i,|((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-μ.real (C i)|)+
        ((n : ℝ)-(S.card : ℝ))/(n : ℝ)) := by
  classical
  have hb' : ∀ z, 0 ≤ M-f z ∧ M-f z ≤ M := fun z => ⟨by linarith [(hb z).2],by linarith [(hb z).1]⟩
  have hv' : ∀ j, 0 ≤ M-v j ∧ M-v j ≤ M := fun j => ⟨by linarith [(hv j).2],by linarith [(hv j).1]⟩
  have hh := partition_upper μ hn C hC hdisj hcover s S
    (fun z => M-f z) (fun j => M-v j) M e hM he ((integrable_const M).sub hf) hb' hv'
    (fun j hj i hi z hz => by linarith [hr j hj i hi z hz])
  rw [integral_sub (integrable_const M) hf] at hh
  simp only [integral_const,probReal_univ,one_smul,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,sub_div] at hh
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hcancel : (n : ℝ)*M/(n : ℝ)=M := by field_simp
  rw [hcancel] at hh
  simp only [sub_div]
  linarith

end XuPseudoHelpers
open Classical MeasureTheory Filter
open XuMannorRobust.Quantile
open scoped BigOperators
noncomputable section
namespace XuPseudoHelpers

theorem empirical_prob {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (s : Fin n → Z) : IsProbabilityMeasure (empiricalMeasure s) := by
  constructor
  simp only [empiricalMeasure,Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by finiteness)

theorem empirical_integral {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (s : Fin n → Z) (f : Z → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂empiricalMeasure s) = (∑ j,f (s j))/(n : ℝ) := by
  rw [empiricalMeasure,integral_smul_measure]
  rw [integral_finsetSum_measure (fun j _ => integrable_dirac' hf.stronglyMeasurable (by finiteness))]
  simp [integral_dirac' f _ hf.stronglyMeasurable,ENNReal.toReal_inv,div_eq_mul_inv,mul_comm]

end XuPseudoHelpers
namespace XuPseudoHelpers

theorem law_cdf {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (f : Z → ℝ) (hf : Measurable f) (x : ℝ) :
    (μ.map f).real (Set.Iic x) = ∫ z,if f z ≤ x then (1 : ℝ) else 0 ∂μ := by
  rw [measureReal_def,Measure.map_apply hf measurableSet_Iic,← measureReal_def]
  have hh := integral_indicator_const (μ := μ) (1 : ℝ) (measurableSet_le hf (measurable_const (a := x)))
  convert! hh.symm using 1 <;> simp [Set.indicator_apply,smul_eq_mul]
  congr 1

theorem law_cap {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (f : Z → ℝ) (hf : Measurable f) (t : ℝ) :
    (∫ x,min x t ∂μ.map f) = ∫ z,min (f z) t ∂μ := by
  exact integral_map hf.aemeasurable (continuous_id.min continuous_const).aestronglyMeasurable

theorem law_support {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    (f : Z → ℝ) (hf : Measurable f) (hpos : ∀ z,0 ≤ f z) :
    (μ.map f) (Set.Iio 0)=0 := by
  rw [Measure.map_apply hf measurableSet_Iio]
  have he : f ⁻¹' Set.Iio 0 = ∅ := by ext z; simp; exact hpos z
  rw [he,measure_empty]

theorem law_bounded {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (f : Z → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ z,f z ≤ M) :
    (μ.map f) (Set.Iic M)=1 := by
  rw [Measure.map_apply hf measurableSet_Iic]
  have he : f ⁻¹' Set.Iic M = Set.univ := by ext z; simp; exact hb z
  rw [he,measure_univ]

private theorem bounded_integrable {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : Measurable f) (M : ℝ)
    (hb : ∀ z,0 ≤ f z ∧ f z ≤ M) : Integrable f μ := by
  apply (integrable_const M).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hb z).1] using (hb z).2

theorem pseudo_distribution_bounds {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {n K : ℕ} (hn : 0 < n) (C : Fin K → Set Z)
    (hC : ∀ i,MeasurableSet (C i)) (hdisj : Pairwise (Function.onFun Disjoint C))
    (hcover : (⋃ i,C i)=Set.univ) (s : Fin n → Z) (S : Finset (Fin n))
    (f : Z → ℝ) (hf : Measurable f) (hpos : ∀ z,0 ≤ f z)
    (e : ℝ) (he : 0 ≤ e)
    (hr : ∀ j ∈ S,∀ i,s j ∈ C i → ∀ z ∈ C i,|f (s j)-f z| ≤ e) :
    let P := μ.map f
    let Q := (empiricalMeasure s).map f
    let a := (∑ i,|((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-μ.real (C i)|)+
        ((n : ℝ)-(S.card : ℝ))/(n : ℝ)
    (∀ x : ℝ,P.real (Set.Iic x) ≤ Q.real (Set.Iic (x+e))+a) ∧
    (∀ x : ℝ,Q.real (Set.Iic x) ≤ P.real (Set.Iic (x+e))+a) ∧
    (∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂P) ≤ (∫ x,min x t ∂Q)+e+a*t) ∧
    (∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂Q) ≤ (∫ x,min x t ∂P)+e+a*t) := by
  classical
  dsimp only
  have hcdfmeas (x : ℝ) : Measurable (fun z => if f z ≤ x then (1 : ℝ) else 0) := by
    have hh : Measurable ({z | f z ≤ x}.indicator (fun _ : Z => (1 : ℝ))) :=
      measurable_const.indicator (measurableSet_le hf (measurable_const (a := x)))
    convert! hh using 1
  have hcdfbound (x : ℝ) (z : Z) :
      0 ≤ (if f z ≤ x then (1 : ℝ) else 0) ∧ (if f z ≤ x then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hi (x : ℝ) : Integrable (fun z => if f z ≤ x then (1 : ℝ) else 0) μ :=
    bounded_integrable μ _ (hcdfmeas x) 1 (hcdfbound x)
  have hcapmeas (t : ℝ) : Measurable (fun z => min (f z) t) := hf.min measurable_const
  have hcapbound (t : ℝ) (ht : 0 ≤ t) (z : Z) : 0 ≤ min (f z) t ∧ min (f z) t ≤ t :=
    ⟨le_min (hpos z) ht,min_le_right _ _⟩
  have hcapclose (t : ℝ) (j : Fin n) (hj : j ∈ S) (i : Fin K) (hji : s j ∈ C i)
      (z : Z) (hz : z ∈ C i) : |min (f (s j)) t-min (f z) t| ≤ e := by
    have hh := abs_le.mp (hr j hj i hji z hz)
    apply abs_le.mpr
    simp only [min_def]
    split_ifs <;> constructor <;> linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro x
    have hh := partition_upper μ hn C hC hdisj hcover s S
      (fun z => if f z ≤ x then (1 : ℝ) else 0)
      (fun j => if f (s j) ≤ x+e then (1 : ℝ) else 0) 1 0 (by norm_num) (by norm_num)
      (hi x) (hcdfbound x) (fun j => hcdfbound (x+e) (s j)) ?_
    · rw [law_cdf μ f hf x,law_cdf (empiricalMeasure s) f hf (x+e),empirical_integral s _ (hcdfmeas (x+e))]
      simpa using hh
    · intro j hj i hji z hz
      have hcl := (abs_le.mp (hr j hj i hji z hz)).2
      split_ifs <;> norm_num <;> linarith
  · intro x
    have hh := partition_lower μ hn C hC hdisj hcover s S
      (fun z => if f z ≤ x+e then (1 : ℝ) else 0)
      (fun j => if f (s j) ≤ x then (1 : ℝ) else 0) 1 0 (by norm_num) (by norm_num)
      (hi (x+e)) (hcdfbound (x+e)) (fun j => hcdfbound x (s j)) ?_
    · rw [law_cdf (empiricalMeasure s) f hf x,empirical_integral s _ (hcdfmeas x),law_cdf μ f hf (x+e)]
      simpa using hh
    · intro j hj i hji z hz
      have hcl := (abs_le.mp (hr j hj i hji z hz)).1
      split_ifs <;> norm_num <;> linarith
  · intro t ht
    have hh := partition_upper μ hn C hC hdisj hcover s S (fun z => min (f z) t)
      (fun j => min (f (s j)) t) t e ht he (bounded_integrable μ _ (hcapmeas t) t (hcapbound t ht))
      (hcapbound t ht) (fun j => hcapbound t ht (s j))
      (fun j hj i hji z hz => by have hh := (abs_le.mp (hcapclose t j hj i hji z hz)).1; linarith)
    rw [law_cap μ f hf t,law_cap (empiricalMeasure s) f hf t,empirical_integral s _ (hcapmeas t)]
    simpa [mul_comm t] using hh
  · intro t ht
    have hh := partition_lower μ hn C hC hdisj hcover s S (fun z => min (f z) t)
      (fun j => min (f (s j)) t) t e ht he (bounded_integrable μ _ (hcapmeas t) t (hcapbound t ht))
      (hcapbound t ht) (fun j => hcapbound t ht (s j))
      (fun j hj i hji z hz => by have hh := (abs_le.mp (hcapclose t j hj i hji z hz)).2; linarith)
    rw [law_cap (empiricalMeasure s) f hf t,empirical_integral s _ (hcapmeas t),law_cap μ f hf t]
    simpa [mul_comm t] using hh

end XuPseudoHelpers

namespace XuPseudoHelpers
open XuMannorRobust.Quantile

theorem pseudo_pointwise {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hb : ∀ h z,0 ≤ l h z ∧ l h z ≤ M) (hm : ∀ h,Measurable (l h))
    {n K : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (e : (Fin n → Z) → ℝ)
    (nhat : (Fin n → Z) → ℕ) (hnhat : ∀ s,1 ≤ nhat s ∧ nhat s ≤ n)
    (C : Fin K → Set Z) (hC : ∀ i,MeasurableSet (C i))
    (hdisj : Pairwise (Function.onFun Disjoint C)) (hcover : (⋃ i,C i)=Set.univ)
    (hr : ∀ s,∃ S : Finset (Fin n),S.card=nhat s ∧
      ∀ j ∈ S,∀ z i,s j ∈ C i → z ∈ C i → |l (A s) (s j)-l (A s) z| ≤ e s)
    (s : Fin n → Z) (lam beta : ℝ) (hlam : 0 ≤ lam) (hb0 : 0 < beta) (hb1 : beta < 1)
    (hdev : (∑ i,|((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-μ.real (C i)|) ≤ lam)
    (hlevels : 0 ≤ beta-lam-((n : ℝ)-(nhat s : ℝ))/(n : ℝ) ∧
      beta+lam+((n : ℝ)-(nhat s : ℝ))/(n : ℝ) ≤ 1) :
    (lossQuantile l (A s) (beta-lam-((n : ℝ)-(nhat s : ℝ))/(n : ℝ)) (empiricalMeasure s)-e s ≤
        lossQuantile l (A s) beta μ ∧
      lossQuantile l (A s) beta μ ≤
        lossQuantile l (A s) (beta+lam+((n : ℝ)-(nhat s : ℝ))/(n : ℝ)) (empiricalMeasure s)+e s) ∧
    (lossTruncatedMean l (A s) (beta-lam-((n : ℝ)-(nhat s : ℝ))/(n : ℝ)) (empiricalMeasure s)-e s ≤
        lossTruncatedMean l (A s) beta μ ∧
      lossTruncatedMean l (A s) beta μ ≤
        lossTruncatedMean l (A s) (beta+lam+((n : ℝ)-(nhat s : ℝ))/(n : ℝ)) (empiricalMeasure s)+e s) := by
  classical
  obtain ⟨S,hS,hrob⟩ := hr s
  have hSpos : 0 < S.card := by rw [hS]; exact lt_of_lt_of_le Nat.zero_lt_one (hnhat s).1
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hSpos
  have hcov (z : Z) : ∃ i,z ∈ C i := by apply Set.mem_iUnion.mp; rw [hcover]; trivial
  obtain ⟨i,hi⟩ := hcov (s j)
  have he : 0 ≤ e s := by simpa using hrob j hj (s j) i hi hi
  let P := μ.map (l (A s))
  let Q := (empiricalMeasure s).map (l (A s))
  let r := ((n : ℝ)-(nhat s : ℝ))/(n : ℝ)
  let a := lam+r
  have hr0 : 0 ≤ r := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    exact sub_nonneg.mpr (by exact_mod_cast (hnhat s).2)
  have ha : 0 ≤ a := add_nonneg hlam hr0
  have hlow : 0 ≤ beta-a := by dsimp [a,r]; linarith [hlevels.1]
  have hhigh : beta+a ≤ 1 := by dsimp [a,r]; linarith [hlevels.2]
  letI : IsProbabilityMeasure (empiricalMeasure s) := empirical_prob hn s
  letI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map (hm (A s)).aemeasurable
  letI : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (hm (A s)).aemeasurable
  have hP : P (Set.Iio 0)=0 := law_support μ _ (hm (A s)) (fun z => (hb (A s) z).1)
  have hQ : Q (Set.Iio 0)=0 := law_support (empiricalMeasure s) _ (hm (A s)) (fun z => (hb (A s) z).1)
  have hPfin : ∃ M : ℝ,P (Set.Iic M)=1 := ⟨M,law_bounded μ _ (hm (A s)) M (fun z => (hb (A s) z).2)⟩
  have hQfin : ∃ M : ℝ,Q (Set.Iic M)=1 := ⟨M,law_bounded (empiricalMeasure s) _ (hm (A s)) M (fun z => (hb (A s) z).2)⟩
  have hd := pseudo_distribution_bounds μ hn C hC hdisj hcover s S (l (A s)) (hm (A s))
    (fun z => (hb (A s) z).1) (e s) he (fun j hj i hji z hz => hrob j hj z i hji hz)
  dsimp only at hd
  rw [hS] at hd
  have hPQ : ∀ x : ℝ,P.real (Set.Iic x) ≤ Q.real (Set.Iic (x+e s))+a := by
    intro x
    have hh := hd.1 x
    dsimp [P,Q,a,r]
    linarith
  have hQP : ∀ x : ℝ,Q.real (Set.Iic x) ≤ P.real (Set.Iic (x+e s))+a := by
    intro x
    have hh := hd.2.1 x
    dsimp [P,Q,a,r]
    linarith
  have hcapPQ : ∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂P) ≤ (∫ x,min x t ∂Q)+e s+a*t := by
    intro t ht
    have hh := hd.2.2.1 t ht
    have hmul := mul_le_mul_of_nonneg_right hdev ht
    dsimp [P,Q,a,r]
    nlinarith
  have hcapQP : ∀ t : ℝ,0 ≤ t → (∫ x,min x t ∂Q) ≤ (∫ x,min x t ∂P)+e s+a*t := by
    intro t ht
    have hh := hd.2.2.2 t ht
    have hmul := mul_le_mul_of_nonneg_right hdev ht
    dsimp [P,Q,a,r]
    nlinarith
  have hq := quantile_shift_bounds P Q hP hQ hPfin hQfin beta a (e s) hb0 hb1 ha he hlow hhigh hPQ hQP
  have ht := truncated_shift_bounds P Q hP hQ hPfin hQfin beta a (e s) hb0.le ha hlow hhigh hcapPQ hcapQP
  have hloeq : beta-lam-((n : ℝ)-(nhat s : ℝ))/(n : ℝ)=beta-a := by dsimp [a,r]; ring
  have hhieq : beta+lam+((n : ℝ)-(nhat s : ℝ))/(n : ℝ)=beta+a := by dsimp [a,r]; ring
  simpa only [hloeq,hhieq,lossQuantile,lossTruncatedMean] using And.intro hq ht

end XuPseudoHelpers

open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

private theorem bounded_average_tail {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : Measurable f)
    (hb : ∀ z, f z ∈ Set.Icc (-1) 1) {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi (fun _ : Fin n => μ)) {s | lam ≤ (∑ j, f (s j)) / (n : ℝ) - ∫ z, f z ∂μ} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let X (j : Fin n) (s : Fin n → Z) := f (s j) - ∫ z, f z ∂μ
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => (hf.sub_const _).aemeasurable)
  have hsub (j : Fin n) : HasSubgaussianMGF (X j) 1 P := by
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := P)
      (X := fun s : Fin n → Z => f (s j)) (hf.comp (measurable_pi_apply j)).aemeasurable
      (Filter.Eventually.of_forall fun s => hb (s j))
    rw [integral_comp_eval (μ := fun _ : Fin n => μ) hf.aestronglyMeasurable] at hh
    norm_num at hh
    exact hh
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hh := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => (1 : NNReal)) (fun j _ => hsub j)
    (show 0 ≤ (n : ℝ)*lam from mul_nonneg hn'.le hlam)
  have heq : {s : Fin n → Z | lam ≤ (∑ j, f (s j))/(n : ℝ) - ∫ z, f z ∂μ} =
      {s | (n : ℝ)*lam ≤ ∑ j, X j s} := by
    ext s
    simp only [Set.mem_setOf_eq, X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hc : (∑ j, f (s j))/(n : ℝ)*(n : ℝ) = ∑ j, f (s j) := div_mul_cancel₀ _ hn'.ne'
    constructor <;> intro h <;> nlinarith
  rw [heq]
  rw [← ofReal_measureReal (μ := P)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, NNReal.coe_natCast] at hh
  have he : -((n : ℝ)*lam)^2/(2*(n : ℝ)) = -((n : ℝ)*lam^2)/2 := by field_simp
  simpa only [he] using hh

private theorem bhc {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n => μ)
        {s | lam ≤ ∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ) / (n : ℝ) - (μ (C i)).toReal|}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ K * Real.exp (-((n : ℝ) * lam ^ 2) / 2)) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let sign (σ : Fin K → Bool) (i : Fin K) : ℝ := if σ i then 1 else -1
  let g (σ : Fin K → Bool) (z : Z) := ∑ i, (C i).indicator (fun _ => sign σ i) z
  have hg (σ : Fin K → Bool) : Measurable (g σ) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator (hC_meas i)
  have hgi (σ : Fin K → Bool) (z : Z) (i : Fin K) (hi : z ∈ C i) : g σ z = sign σ i := by
    dsimp only [g]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      have hj : z ∉ C j := fun hj => Set.disjoint_left.mp (hC_disj hji) hj hi
      exact Set.indicator_of_notMem hj _
    · simp
  have hgb (σ : Fin K → Bool) (z : Z) : g σ z ∈ Set.Icc (-1) 1 := by
    obtain ⟨i, hi⟩ : ∃ i, z ∈ C i := by
      apply Set.mem_iUnion.mp
      rw [hC_cover]
      trivial
    rw [hgi σ z i hi]
    dsimp [sign]
    split <;> norm_num
  have hmean (σ : Fin K → Bool) : ∫ z, g σ z ∂μ = ∑ i, μ.real (C i) * sign σ i := by
    rw [show g σ = fun z => ∑ i, (C i).indicator (fun _ => sign σ i) z from rfl, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      simpa using integral_indicator_const (μ := μ) (sign σ i) (hC_meas i)
    · intro i _
      exact (integrable_const _).indicator (hC_meas i)
  have hsample (σ : Fin K → Bool) (s : Fin n → Z) :
      (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ =
      ∑ i, sign σ i * (((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - μ.real (C i)) := by
    dsimp only [g]
    rw [Finset.sum_comm]
    have hh (i : Fin K) : (∑ j, (C i).indicator (fun _ => sign σ i) (s j)) =
        ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ) * sign σ i := by
      simp only [Set.indicator_apply, ← Finset.sum_filter]
      simp
    simp_rw [hh]
    change (∑ i, ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)*sign σ i)/(n : ℝ) - ∫ z, g σ z ∂μ = _
    rw [hmean, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  let E (σ : Fin K → Bool) := {s : Fin n → Z | lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ}
  have hsub : {s : Fin n → Z | lam ≤ ∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - (μ (C i)).toReal|} ⊆ ⋃ σ, E σ := by
    intro s hs
    let σ (i : Fin K) : Bool := decide (0 ≤ ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - μ.real (C i))
    apply Set.mem_iUnion.mpr
    refine ⟨σ, ?_⟩
    change lam ≤ (∑ j, g σ (s j))/(n : ℝ) - ∫ z, g σ z ∂μ
    rw [hsample]
    change lam ≤ ∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - (μ (C i)).toReal| at hs
    convert hs using 1
    congr 1
    funext i
    dsimp only [sign, σ]
    split <;> rename_i hi
    · have hh : 0 ≤ ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - μ.real (C i) := of_decide_eq_true hi
      change 0 ≤ ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [one_mul, abs_of_nonneg hh]
      rfl
    · have hh : ¬0 ≤ ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - μ.real (C i) := fun h => hi (by simp [h])
      change ¬0 ≤ ((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ) - (μ (C i)).toReal at hh
      rw [neg_one_mul, abs_of_neg (lt_of_not_ge hh)]
      rfl
  calc
    _ ≤ P (⋃ σ, E σ) := measure_mono hsub
    _ ≤ ∑' σ, P (E σ) := measure_iUnion_le _
    _ = ∑ σ, P (E σ) := tsum_fintype _
    _ ≤ ∑ σ : Fin K → Bool, ENNReal.ofReal (Real.exp (-((n : ℝ)*lam^2)/2)) := by
      apply Finset.sum_le_sum
      intro σ _
      exact bounded_average_tail μ (g σ) (hg σ) (hgb σ) hn lam hlam
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        simp [Fintype.card_fun, Fintype.card_fin]
      · intro σ _
        exact (Real.exp_pos _).le

theorem XuPseudoHelpers.partition_event_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ) / (n : ℝ) - (μ (C i)).toReal|
            ≤ Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  by_cases hd : 1 ≤ δ
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hd)
  have hd1 : δ < 1 := lt_of_not_ge hd
  let x := (2*(K : ℝ)*Real.log 2 + 2*Real.log (1/δ))/(n : ℝ)
  have hx : 0 ≤ x := by
    apply div_nonneg _ (Nat.cast_nonneg n)
    have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hld : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
    positivity
  have hb := bhc μ C hC_meas hC_disj hC_cover hn (Real.sqrt x) (Real.sqrt_nonneg x)
  have hsub : {s : Fin n → Z | ¬(∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-(μ (C i)).toReal| ≤ Real.sqrt x)} ⊆
      {s | Real.sqrt x ≤ ∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ)/(n : ℝ)-(μ (C i)).toReal|} :=
    fun s hs => (lt_of_not_ge hs).le
  apply (measure_mono hsub).trans
  have he : (2 : ℝ)^K * Real.exp (-((n : ℝ)*(Real.sqrt x)^2)/2) = δ := by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    have heq : -((n : ℝ)*(Real.sqrt x)^2)/2 = -((K : ℝ)*Real.log 2) + Real.log δ := by
      rw [Real.sq_sqrt hx]
      dsimp [x]
      rw [Real.log_div (by norm_num) hδ.ne', Real.log_one]
      field_simp
      ring
    rw [heq, Real.exp_add, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log hδ]
    field_simp
  rwa [he] at hb

namespace XuMannorRobust.Quantile
theorem _root_.solution {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H) (K : ℕ) (ε : (Fin n → Z) → ℝ)
    (nhat : (Fin n → Z) → ℕ) (hA : IsPseudoRobust l A K ε nhat)
    (δ : ℝ) (hδ : 0 < δ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (Measure.pi fun _ : Fin n => μ)
        {s : Fin n → Z | ¬
          ((0 ≤ β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ) ∧
            β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ) ≤ 1) →
          -- (I) quantile value
          ((lossQuantile l (A s)
                (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) - ε s
              ≤ lossQuantile l (A s) β μ ∧
            lossQuantile l (A s) β μ
              ≤ lossQuantile l (A s)
                (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) + ε s) ∧
          -- (II) truncated mean
          (lossTruncatedMean l (A s)
                (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  - ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) - ε s
              ≤ lossTruncatedMean l (A s) β μ ∧
            lossTruncatedMean l (A s) β μ
              ≤ lossTruncatedMean l (A s)
                (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))
                  + ((n : ℝ) - (nhat s : ℝ)) / (n : ℝ)) (empiricalMeasure s) + ε s)))}
      ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨hnhat,C,hC,hdisj,hcover,hrob⟩ := hA
  refine le_trans (measure_mono ?_) (XuPseudoHelpers.partition_event_bound μ C hC hdisj hcover hn δ hδ)
  intro s hs hdev
  apply hs
  intro hlevels
  exact XuPseudoHelpers.pseudo_pointwise μ l M hl_bound hl_meas hn A ε nhat hnhat C hC hdisj hcover hrob s
    (Real.sqrt ((2*(K : ℝ)*Real.log 2+2*Real.log (1/δ))/(n : ℝ))) β
    (Real.sqrt_nonneg _) hβ0 hβ1 hdev hlevels

end XuMannorRobust.Quantile
