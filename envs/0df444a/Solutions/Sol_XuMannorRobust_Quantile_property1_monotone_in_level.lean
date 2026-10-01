-- Prove2me | solution 1 for XuMannorRobust.Quantile.property1_monotone_in_level
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:55:47.32598+00:00
-- url     : https://prove2.me/submissions/b86eacbe-cf8e-45fc-9d81-005c8ba21b06

import Definitions.Def_XuMannorRobust_Quantile_QuantileTruncatedMean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Layercake

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
open XuMannorRobust.Quantile

/-- **Appendix C, property 1** (Xu & Mannor 2012, p. 415). Let `X` be a random variable with law
`P`, supported on `ℝ⁺` (`P((-∞, 0)) = 0`). If `0 ≤ β₂ ≤ β₁ ≤ 1`, then `ℚ^{β₁}(X) ≥ ℚ^{β₂}(X)` and
`𝕋^{β₁}(X) ≥ 𝕋^{β₂}(X)`. The top level `β₁ = 1` is allowed only when `X` is bounded above
(`P((-∞, M]) = 1` for some `M`): for unbounded `X` the paper's `ℚ¹(X)` is `+∞`, which Lean's real
`sInf ∅ = 0` cannot represent. -/
theorem solution (P : Measure ℝ) [IsProbabilityMeasure P]
    (hP : P (Set.Iio 0) = 0) (β₁ β₂ : ℝ) (hβ₂ : 0 ≤ β₂) (h21 : β₂ ≤ β₁) (hβ₁ : β₁ ≤ 1)
    (hfin : β₁ < 1 ∨ ∃ M : ℝ, P (Set.Iic M) = 1) :
    quantileValue P β₂ ≤ quantileValue P β₁ ∧ truncatedMean P β₂ ≤ truncatedMean P β₁ := by
  exact ⟨XuProof.q_mono P hP β₁ β₂ hβ₂ h21 hβ₁ hfin, XuProof.truncated_mono P hP β₁ β₂ hβ₂ h21 hβ₁ hfin⟩


