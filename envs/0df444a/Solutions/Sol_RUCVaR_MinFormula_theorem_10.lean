-- Prove2me | solution 1 for RUCVaR.MinFormula.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T05:31:08.215323+00:00
-- url     : https://prove2.me/submissions/6c873573-25a3-4c41-9e5f-789a008b152c

-- Licensed under Apache 2.0. Complete CVaR tail-mean minimization theorem.
import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RUCVaR_MinFormula_Setting
open MeasureTheory Filter Topology


namespace CVaRProof

open MeasureTheory

noncomputable def lowerQuantile (ν : Measure ℝ) (β : ℝ) : ℝ :=
  sInf {a : ℝ | β ≤ ν.real (Set.Iic a)}

noncomputable def upperQuantile (ν : Measure ℝ) (β : ℝ) : ℝ :=
  sInf {a : ℝ | β < ν.real (Set.Iic a)}

noncomputable def scalarObjective (ν : Measure ℝ) (β a : ℝ) : ℝ :=
  a + (1 - β)⁻¹ * ∫ z, max (z - a) 0 ∂ν

end CVaRProof


namespace CVaRProof

open MeasureTheory

lemma hinge_difference_le (z a b : ℝ) :
    max (z - a) 0 - max (z - b) 0 ≤ |a - b| := by
  have hab : b - a ≤ |a - b| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have h0 : 0 ≤ |a - b| := abs_nonneg _
  have h1 := le_max_left (z - b) 0
  have h2 := le_max_right (z - b) 0
  apply sub_le_iff_le_add.mpr
  apply max_le <;> linarith

lemma hinge_abs_difference (z a b : ℝ) :
    |max (z - a) 0 - max (z - b) 0| ≤ |a - b| := by
  apply abs_le.mpr
  constructor
  · have h := hinge_difference_le z b a
    rw [abs_sub_comm b a] at h
    linarith
  · exact hinge_difference_le z a b

lemma hinge_chord_lower (z a b : ℝ) (hab : a ≤ b) :
    -(b - a) * (if a < z then 1 else 0) ≤
      max (z - b) 0 - max (z - a) 0 := by
  split_ifs with hz
  · by_cases hzb : b ≤ z
    · rw [max_eq_left (by linarith : 0 ≤ z - b),
        max_eq_left (by linarith : 0 ≤ z - a)]
      ring_nf
      exact le_refl _
    · rw [max_eq_right (by linarith : z - b ≤ 0),
        max_eq_left (by linarith : 0 ≤ z - a)]
      linarith
  · rw [max_eq_right (by linarith : z - b ≤ 0),
      max_eq_right (by linarith : z - a ≤ 0)]
    simp

lemma hinge_chord_upper (z a b : ℝ) (hab : a ≤ b) :
    max (z - b) 0 - max (z - a) 0 ≤
      -(b - a) * (if b ≤ z then 1 else 0) := by
  split_ifs with hz
  · rw [max_eq_left (by linarith : 0 ≤ z - b),
      max_eq_left (by linarith : 0 ≤ z - a)]
    ring_nf
    exact le_refl _
  · rw [max_eq_right (by linarith : z - b ≤ 0)]
    have h := le_max_right (z - a) 0
    simp only [mul_zero]
    linarith

lemma hinge_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) (a : ℝ) :
    Integrable (fun z => max (z - a) 0) ν := by
  exact (hi.sub (integrable_const a)).sup (integrable_const 0)

end CVaRProof


namespace CVaRProof

open MeasureTheory

lemma hinge_convex (z x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    max (z - (a * x + b * y)) 0 ≤ a * max (z - x) 0 + b * max (z - y) 0 := by
  have hxa := mul_le_mul_of_nonneg_left (le_max_left (z-x) 0) ha
  have hyb := mul_le_mul_of_nonneg_left (le_max_left (z-y) 0) hb
  have hxa0 := mul_nonneg ha (le_max_right (z-x) 0)
  have hyb0 := mul_nonneg hb (le_max_right (z-y) 0)
  have hz := congrArg (fun t : ℝ => t * z) hab
  apply max_le <;> nlinarith

lemma scalarObjective_convex (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β : ℝ} (hβ : β < 1) :
    ConvexOn ℝ Set.univ (scalarObjective ν β) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := integral_mono (hinge_integrable ν hi (a*x+b*y))
    (((hinge_integrable ν hi x).const_mul a).add ((hinge_integrable ν hi y).const_mul b))
    (fun z => hinge_convex z x y a b ha hb hab)
  simp only [Pi.add_def, integral_add ((hinge_integrable ν hi x).const_mul a)
    ((hinge_integrable ν hi y).const_mul b), integral_const_mul] at h
  have hp : 0 ≤ (1-β)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hβ).le
  have hh := mul_le_mul_of_nonneg_left h hp
  simp only [scalarObjective, smul_eq_mul]
  nlinarith

lemma scalarObjective_continuous (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β : ℝ} (hβ : β < 1) :
    Continuous (scalarObjective ν β) := by
  exact continuousOn_univ.mp ((scalarObjective_convex ν hi hβ).continuousOn isOpen_univ)

end CVaRProof


namespace CVaRProof

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

theorem cdf_left_eq (a : ℝ) : Function.leftLim (cdf ν) a = ν.real (Iio a) := by
  have hn : 0 ≤ Function.leftLim (cdf ν) a :=
    (cdf_nonneg ν (a - 1)).trans ((monotone_cdf ν).le_leftLim (by linarith))
  have he := (cdf ν).measure_Iio (tendsto_cdf_atBot ν) a
  rw [measure_cdf ν, sub_zero] at he
  rw [measureReal_def, he, ENNReal.toReal_ofReal hn]

theorem cdf_left_tendsto (a : ℝ) :
    Tendsto (fun b => ν.real (Iic b)) (𝓝[<] a) (𝓝 (ν.real (Iio a))) := by
  have h := (monotone_cdf ν).tendsto_leftLim a
  rw [cdf_left_eq] at h
  exact h.congr (fun b => cdf_eq_real ν b)

theorem cdf_right_tendsto (a : ℝ) :
    Tendsto (fun b => ν.real (Iic b)) (𝓝[>] a) (𝓝 (ν.real (Iic a))) := by
  have h : Tendsto (cdf ν) (𝓝[>] a) (𝓝 (cdf ν a)) :=
    ((cdf ν).right_continuous a).mono Ioi_subset_Ici_self
  rw [cdf_eq_real] at h
  exact h.congr (fun b => cdf_eq_real ν b)

theorem cdf_below_exists {β : ℝ} (hβ : 0 < β) :
    ∃ a : ℝ, ν.real (Iic a) < β := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds hβ)).exists
  exact ⟨a, by simpa only [cdf_eq_real] using ha⟩

theorem cdf_above_exists {β : ℝ} (hβ : β < 1) :
    ∃ a : ℝ, β < ν.real (Iic a) := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds hβ)).exists
  exact ⟨a, by simpa only [cdf_eq_real] using ha⟩

theorem quantile_sets {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ({a : ℝ | β ≤ ν.real (Iic a)}).Nonempty ∧
    BddBelow {a : ℝ | β ≤ ν.real (Iic a)} ∧
    ({a : ℝ | β < ν.real (Iic a)}).Nonempty ∧
    BddBelow {a : ℝ | β < ν.real (Iic a)} := by
  obtain ⟨a, ha⟩ := cdf_below_exists ν hβ0
  obtain ⟨b, hb⟩ := cdf_above_exists ν hβ1
  have hlow : ∀ z, β ≤ ν.real (Iic z) → a ≤ z := by
    intro z hz
    by_contra hn
    have hm := (monotone_cdf ν) (le_of_lt (lt_of_not_ge hn))
    rw [cdf_eq_real, cdf_eq_real] at hm
    linarith
  exact ⟨⟨b, hb.le⟩, ⟨a, fun z hz => hlow z hz⟩,
    ⟨b, hb⟩, ⟨a, fun z hz => hlow z hz.le⟩⟩

theorem cdf_left_le_cdf (a : ℝ) : ν.real (Iio a) ≤ ν.real (Iic a) := by
  exact measureReal_mono Iio_subset_Iic_self

theorem cdf_le_left {a b : ℝ} (hab : a < b) :
    ν.real (Iic a) ≤ ν.real (Iio b) := by
  exact measureReal_mono (Iic_subset_Iio.mpr hab)

theorem cdf_right_witness {a β : ℝ} (h : ν.real (Iic a) < β) :
    ∃ b, a < b ∧ ν.real (Iic b) < β := by
  have he := (cdf_right_tendsto ν a).eventually (gt_mem_nhds h)
  have hs : ∀ᶠ b in 𝓝[>] a, a < b := self_mem_nhdsWithin
  obtain ⟨b, hb, hc⟩ := (hs.and he).exists
  exact ⟨b, hb, hc⟩

theorem cdf_left_witness {a β : ℝ} (h : β < ν.real (Iio a)) :
    ∃ b, b < a ∧ β < ν.real (Iic b) := by
  have he := (cdf_left_tendsto ν a).eventually (lt_mem_nhds h)
  have hs : ∀ᶠ b in 𝓝[<] a, b < a := self_mem_nhdsWithin
  obtain ⟨b, hb, hc⟩ := (hs.and he).exists
  exact ⟨b, hb, hc⟩

end CVaRProof


namespace CVaRProof

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] {β : ℝ}

theorem lowerQuantile_le_iff (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℝ) :
    lowerQuantile ν β ≤ a ↔ β ≤ ν.real (Iic a) := by
  obtain ⟨hne, hbd, _, _⟩ := quantile_sets ν hβ0 hβ1
  have hstrict : ∀ b, lowerQuantile ν β < b → β ≤ ν.real (Iic b) := by
    intro b hb
    obtain ⟨c, hc, hcb⟩ := exists_lt_of_csInf_lt hne hb
    exact hc.trans (by simpa only [cdf_eq_real] using (monotone_cdf ν) hcb.le)
  have hq : β ≤ ν.real (Iic (lowerQuantile ν β)) := by
    apply ge_of_tendsto (cdf_right_tendsto ν (lowerQuantile ν β))
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact hstrict b hb
  constructor
  · intro ha
    exact hq.trans (by simpa only [cdf_eq_real] using (monotone_cdf ν) ha)
  · intro ha
    exact csInf_le hbd ha

theorem le_upperQuantile_iff (hβ0 : 0 < β) (hβ1 : β < 1) (a : ℝ) :
    a ≤ upperQuantile ν β ↔ ν.real (Iio a) ≤ β := by
  obtain ⟨_, _, hne, hbd⟩ := quantile_sets ν hβ0 hβ1
  constructor
  · intro ha
    apply le_of_tendsto (cdf_left_tendsto ν a)
    filter_upwards [self_mem_nhdsWithin] with b hb
    apply le_of_not_gt
    intro hh
    have hle : upperQuantile ν β ≤ b := csInf_le hbd hh
    exact (not_le_of_gt hb) (ha.trans hle)
  · intro ha
    by_contra hn
    obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt hne (lt_of_not_ge hn)
    exact (not_lt_of_ge ((cdf_le_left ν hba).trans ha)) hb

theorem lowerQuantile_left (hβ0 : 0 < β) (hβ1 : β < 1) :
    ν.real (Iio (lowerQuantile ν β)) ≤ β := by
  apply le_of_tendsto (cdf_left_tendsto ν (lowerQuantile ν β))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (lt_of_not_ge (fun h => (not_le_of_gt ha)
    ((lowerQuantile_le_iff ν hβ0 hβ1 a).mpr h))).le

theorem quantile_interval (hβ0 : 0 < β) (hβ1 : β < 1) :
    lowerQuantile ν β ≤ upperQuantile ν β ∧
    ∀ a, (ν.real (Iio a) ≤ β ∧ β ≤ ν.real (Iic a)) ↔
      a ∈ Icc (lowerQuantile ν β) (upperQuantile ν β) := by
  refine ⟨(le_upperQuantile_iff ν hβ0 hβ1 _).mpr
    (lowerQuantile_left ν hβ0 hβ1), ?_⟩
  intro a
  rw [mem_Icc, lowerQuantile_le_iff ν hβ0 hβ1,
    le_upperQuantile_iff ν hβ0 hβ1]
  exact and_comm

end CVaRProof


namespace CVaRProof

open MeasureTheory Set

lemma integral_indicator_one (ν : Measure ℝ) (s : Set ℝ) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    ∫ z, (if z ∈ s then (1 : ℝ) else 0) ∂ν = ν.real s := by
  simpa [Set.indicator_apply] using
    (integral_indicator (μ := ν) (f := fun _ : ℝ => (1 : ℝ)) hs)

lemma scalarObjective_chord (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β a b : ℝ} (hβ : β < 1) (hab : a ≤ b) :
    (b-a)*(ν.real (Iic a)-β)/(1-β) ≤ scalarObjective ν β b - scalarObjective ν β a ∧
    scalarObjective ν β b - scalarObjective ν β a ≤ (b-a)*(ν.real (Iio b)-β)/(1-β) := by
  have ia : Integrable (fun z : ℝ => if a < z then (1 : ℝ) else 0) ν :=
    (integrable_const 1).indicator measurableSet_Ioi
  have ib : Integrable (fun z : ℝ => if b ≤ z then (1 : ℝ) else 0) ν :=
    (integrable_const 1).indicator measurableSet_Ici
  have hd := (hinge_integrable ν hi b).sub (hinge_integrable ν hi a)
  have hlo := integral_mono (ia.const_mul (-(b-a))) hd (fun z => hinge_chord_lower z a b hab)
  have hup := integral_mono hd (ib.const_mul (-(b-a))) (fun z => hinge_chord_upper z a b hab)
  simp only [Pi.sub_apply] at hlo hup
  rw [integral_const_mul, integral_sub (hinge_integrable ν hi b) (hinge_integrable ν hi a)] at hlo
  rw [integral_const_mul, integral_sub (hinge_integrable ν hi b) (hinge_integrable ν hi a)] at hup
  have hea : (∫ z : ℝ, (if a < z then (1 : ℝ) else 0) ∂ν) = 1-ν.real (Iic a) := by
    have h := integral_indicator_one ν (Ioi a) measurableSet_Ioi
    simp only [mem_Ioi] at h
    rw [h, ← compl_Iic,
      measureReal_compl measurableSet_Iic, probReal_univ]
  have heb : (∫ z : ℝ, (if b ≤ z then (1 : ℝ) else 0) ∂ν) = 1-ν.real (Iio b) := by
    have h := integral_indicator_one ν (Ici b) measurableSet_Ici
    simp only [mem_Ici] at h
    rw [h, ← compl_Iio,
      measureReal_compl measurableSet_Iio, probReal_univ]
  rw [hea] at hlo
  rw [heb] at hup
  have hp : 0 < (1-β)⁻¹ := inv_pos.mpr (sub_pos.mpr hβ)
  have hl := mul_le_mul_of_nonneg_left hlo hp.le
  have hu := mul_le_mul_of_nonneg_left hup hp.le
  have he : (1-β)⁻¹ * (1-β) = 1 := inv_mul_cancel₀ (sub_pos.mpr hβ).ne'
  simp only [scalarObjective, div_eq_mul_inv]
  constructor <;> nlinarith

end CVaRProof


namespace CVaRProof

open MeasureTheory Set

lemma scalarObjective_min_iff (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β : ℝ} (hβ : β < 1) (a : ℝ) :
    IsMinOn (scalarObjective ν β) univ a ↔
      ν.real (Iio a) ≤ β ∧ β ≤ ν.real (Iic a) := by
  have hd : 0 < 1-β := sub_pos.mpr hβ
  constructor
  · intro hm
    constructor
    · by_contra hn
      obtain ⟨b, hba, hb⟩ := cdf_left_witness ν (lt_of_not_ge hn)
      have hc := (scalarObjective_chord ν hi hβ hba.le).1
      have hp : 0 < (a-b)*(ν.real (Iic b)-β)/(1-β) :=
        div_pos (mul_pos (sub_pos.mpr hba) (sub_pos.mpr hb)) hd
      have hh : scalarObjective ν β a ≤ scalarObjective ν β b := hm (mem_univ b)
      linarith
    · by_contra hn
      obtain ⟨b, hab, hb⟩ := cdf_right_witness ν (lt_of_not_ge hn)
      have hc := (scalarObjective_chord ν hi hβ hab.le).2
      have hb' := (cdf_left_le_cdf ν b).trans_lt hb
      have hp : (b-a)*(ν.real (Iio b)-β)/(1-β) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sub_pos.mpr hab) (sub_neg.mpr hb')) hd
      have hh : scalarObjective ν β a ≤ scalarObjective ν β b := hm (mem_univ b)
      linarith
  · rintro ⟨hl, hr⟩ b _
    change scalarObjective ν β a ≤ scalarObjective ν β b
    rcases le_total a b with hab | hba
    · have hc := (scalarObjective_chord ν hi hβ hab).1
      have hp : 0 ≤ (b-a)*(ν.real (Iic a)-β)/(1-β) :=
        div_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hr)) hd.le
      linarith
    · have hc := (scalarObjective_chord ν hi hβ hba).2
      have hp : (a-b)*(ν.real (Iio a)-β)/(1-β) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) (sub_nonpos.mpr hl)) hd.le
      linarith

lemma scalarObjective_argmin (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    {a | IsMinOn (scalarObjective ν β) univ a} =
      Icc (lowerQuantile ν β) (upperQuantile ν β) := by
  ext a
  exact (scalarObjective_min_iff ν hi hβ1 a).trans ((quantile_interval ν hβ0 hβ1).2 a)

lemma scalarObjective_min_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hi : Integrable (fun z : ℝ => z) ν) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsMinOn (scalarObjective ν β) univ (lowerQuantile ν β) := by
  have h := (quantile_interval ν hβ0 hβ1).1
  have hm : lowerQuantile ν β ∈ Icc (lowerQuantile ν β) (upperQuantile ν β) := ⟨le_rfl,h⟩
  rw [← scalarObjective_argmin ν hi hβ0 hβ1] at hm
  exact hm

end CVaRProof


namespace CVaRProof

open MeasureTheory Set

noncomputable def splitTail (ν : Measure ℝ) (β q : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 - β)⁻¹) • ν.restrict (Ioi q) +
    ENNReal.ofReal ((ν.real (Iic q) - β) / (1 - β)) • Measure.dirac q

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] {β q : ℝ}

theorem splitTail_real (hβ : β < 1) (hq : β ≤ ν.real (Iic q)) (s : Set ℝ) :
    (splitTail ν β q).real s = (1 - β)⁻¹ * (ν.restrict (Ioi q)).real s +
      ((ν.real (Iic q) - β) / (1 - β)) * (Measure.dirac q).real s := by
  have h1 : (ENNReal.ofReal ((1 - β)⁻¹) • ν.restrict (Ioi q)) s ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h2 : (ENNReal.ofReal ((ν.real (Iic q) - β) / (1 - β)) • Measure.dirac q) s ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [splitTail, measureReal_add_apply h1 h2]
  simp only [measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr hβ.le)),
    ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hβ.le))]

theorem strict_tail_mass (q : ℝ) : ν.real (Ioi q) = 1 - ν.real (Iic q) := by
  simpa only [compl_Iic] using probReal_compl_eq_one_sub (μ := ν) measurableSet_Iic

theorem splitTail_probability (hβ : β < 1) (hq : β ≤ ν.real (Iic q)) :
    IsProbabilityMeasure (splitTail ν β q) := by
  apply isProbabilityMeasure_iff_real.mpr
  rw [splitTail_real ν hβ hq, measureReal_restrict_apply_univ, strict_tail_mass]
  simp only [probReal_univ, mul_one]
  field_simp [ne_of_gt (sub_pos.mpr hβ)]
  ring

theorem splitTail_cdf (hβ : β < 1) (hq : β ≤ ν.real (Iic q)) (a : ℝ) :
    (splitTail ν β q).real (Iic a) =
      if a < q then 0 else (ν.real (Iic a) - β) / (1 - β) := by
  rw [splitTail_real ν hβ hq, measureReal_restrict_apply measurableSet_Iic]
  by_cases ha : a < q
  · have he : Iic a ∩ Ioi q = (∅ : Set ℝ) := by
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
      intro hz
      linarith [hz.1, hz.2]
    rw [if_pos ha, he, measureReal_empty]
    simp [measureReal_def, ha.not_ge]
  · have hqa : q ≤ a := le_of_not_gt ha
    have he : Iic a ∩ Ioi q = Iic a \ Iic q := by
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, Set.mem_sdiff, not_le]
    rw [if_neg ha, he, measureReal_sdiff (Iic_subset_Iic.mpr hqa) measurableSet_Iic]
    have hd : (Measure.dirac q).real (Iic a) = 1 := by
      simp [measureReal_def, hqa]
    rw [hd]
    ring

end CVaRProof


namespace CVaRProof

open MeasureTheory Set

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] {β q : ℝ}

omit [IsProbabilityMeasure ν] in
theorem splitTail_integrable (hi : Integrable (fun z : ℝ => z) ν) :
    Integrable (fun z : ℝ => z) (splitTail ν β q) := by
  apply integrable_add_measure.mpr
  exact ⟨hi.restrict.smul_measure ENNReal.ofReal_ne_top,
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top⟩

theorem hinge_integral_tail (hi : Integrable (fun z : ℝ => z) ν) (q : ℝ) :
    (∫ z, max (z - q) 0 ∂ν) = (∫ z in Ioi q, z ∂ν) - q * ν.real (Ioi q) := by
  have he : (∫ z in Ioi q, max (z - q) 0 ∂ν) = ∫ z, max (z - q) 0 ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      simp only [mem_Ioi, not_lt] at hz
      exact max_eq_right (sub_nonpos.mpr hz))
  rw [← he]
  calc
    (∫ z in Ioi q, max (z - q) 0 ∂ν) = ∫ z in Ioi q, z - q ∂ν := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      exact max_eq_left (sub_nonneg.mpr hz.le)
    _ = (∫ z in Ioi q, z ∂ν) - q * ν.real (Ioi q) := by
      rw [integral_sub hi.restrict (integrable_const q)]
      simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
      ring

theorem splitTail_mean (hi : Integrable (fun z : ℝ => z) ν)
    (hβ : β < 1) (hq : β ≤ ν.real (Iic q)) :
    (∫ z, z ∂(splitTail ν β q)) = scalarObjective ν β q := by
  have h1 : Integrable (fun z : ℝ => z)
      (ENNReal.ofReal ((1 - β)⁻¹) • ν.restrict (Ioi q)) :=
    hi.restrict.smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable (fun z : ℝ => z)
      (ENNReal.ofReal ((ν.real (Iic q) - β) / (1 - β)) • Measure.dirac q) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [splitTail, integral_add_measure h1 h2]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sub_nonneg.mpr hβ.le)),
    ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hβ.le))]
  rw [scalarObjective, hinge_integral_tail ν hi, strict_tail_mass]
  field_simp [ne_of_gt (sub_pos.mpr hβ)]
  ring

end CVaRProof


namespace CVaRProof

open MeasureTheory ProbabilityTheory Set RUCVaR.MinFormula

variable {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
  (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin n → ℝ)
  (hf : Measurable (f x))

include hf

omit [IsProbabilityMeasure P] in
theorem loss_cdf (a : ℝ) : (P.map (f x)).real (Iic a) = Psi P f x a := by
  rw [map_measureReal_apply hf measurableSet_Iic]
  rfl

omit [IsProbabilityMeasure P] in
theorem loss_cdf_left (a : ℝ) : (P.map (f x)).real (Iio a) = PsiLeft P f x a := by
  rw [map_measureReal_apply hf measurableSet_Iio]
  rfl

theorem lowerQuantile_map (β : ℝ) : lowerQuantile (P.map (f x)) β = VaR P f β x := by
  unfold lowerQuantile VaR MultistageStochastic.valueAtRisk
  congr 1
  ext a
  rw [mem_ofPred_eq, mem_ofPred_eq, loss_cdf P f x hf]
  exact (ENNReal.ofReal_le_iff_le_toReal (by finiteness)).symm

omit [IsProbabilityMeasure P] in
theorem upperQuantile_map (β : ℝ) : upperQuantile (P.map (f x)) β = VaRPlus P f β x := by
  unfold upperQuantile VaRPlus
  congr 1
  ext a
  rw [mem_ofPred_eq, mem_ofPred_eq, loss_cdf P f x hf]

omit [IsProbabilityMeasure P] in
theorem scalarObjective_map (β a : ℝ) :
    scalarObjective (P.map (f x)) β a = Fbeta P f β x a := by
  unfold scalarObjective Fbeta
  rw [integral_map_of_stronglyMeasurable hf (by fun_prop)]

omit [IsProbabilityMeasure P] in
theorem loss_integrable (hi : Integrable (f x) P) :
    Integrable (fun z : ℝ => z) (P.map (f x)) := by
  exact (integrable_map_measure (by fun_prop) hf.aemeasurable).mpr hi

theorem native_tail_eq (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    tailDist P f β x = splitTail (P.map (f x)) β (lowerQuantile (P.map (f x)) β) := by
  let ν := P.map (f x)
  let : IsProbabilityMeasure ν := P.isProbabilityMeasure_map hf.aemeasurable
  have hq : β ≤ ν.real (Iic (lowerQuantile ν β)) :=
    (lowerQuantile_le_iff ν hβ0 hβ1 _).mp le_rfl
  have hw : IsBetaTailDistribution P f β x (splitTail ν β (lowerQuantile ν β)) := by
    refine ⟨splitTail_probability ν hβ1 hq, ?_⟩
    intro a
    rw [splitTail_cdf ν hβ1 hq, PsiBeta]
    change (if a < lowerQuantile (P.map (f x)) β then 0 else
      ((P.map (f x)).real (Iic a) - β) / (1 - β)) = _
    rw [lowerQuantile_map P f x hf, loss_cdf P f x hf]
  have he : ∃ μ, IsBetaTailDistribution P f β x μ := ⟨_, hw⟩
  have hc : IsBetaTailDistribution P f β x (tailDist P f β x) := by
    unfold tailDist
    rw [dif_pos he]
    exact he.choose_spec
  let : IsProbabilityMeasure (tailDist P f β x) := hc.1
  let : IsProbabilityMeasure (splitTail ν β (lowerQuantile ν β)) := hw.1
  apply Measure.eq_of_cdf
  ext a
  rw [cdf_eq_real, cdf_eq_real, hc.2 a, hw.2 a]

theorem native_cvar_eq_objective (hi : Integrable (f x) P)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    CVaR P f β x = scalarObjective (P.map (f x)) β (lowerQuantile (P.map (f x)) β) := by
  let : IsProbabilityMeasure (P.map (f x)) := P.isProbabilityMeasure_map hf.aemeasurable
  rw [CVaR, native_tail_eq P f x hf β hβ0 hβ1]
  exact splitTail_mean _ (loss_integrable P f x hf hi) hβ1
    ((lowerQuantile_le_iff _ hβ0 hβ1 _).mp le_rfl)

end CVaRProof


namespace CVaRProof

open MeasureTheory RUCVaR.MinFormula

theorem full_native_result {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (_hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hx : x ∈ X) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) ∧ Continuous (Fbeta P f β x) ∧
    IsLeast (Set.range (Fbeta P f β x)) (CVaR P f β x) ∧
    (VaR P f β x ≤ VaRPlus P f β x ∧
      {α : ℝ | IsMinOn (Fbeta P f β x) Set.univ α} = Set.Icc (VaR P f β x) (VaRPlus P f β x)) ∧
    (IsMinOn (Fbeta P f β x) Set.univ (VaR P f β x) ∧
      CVaR P f β x = Fbeta P f β x (VaR P f β x)) := by
  let ν := P.map (f x)
  let : IsProbabilityMeasure ν := P.isProbabilityMeasure_map (hf_meas x).aemeasurable
  have hi : Integrable (fun z : ℝ => z) ν := loss_integrable P f x (hf_meas x) (hf_int x hx)
  have he : scalarObjective ν β = Fbeta P f β x := by
    funext a
    exact scalarObjective_map P f x (hf_meas x) β a
  have hq := lowerQuantile_map P f x (hf_meas x) β
  have hr := upperQuantile_map P f x (hf_meas x) β
  have hm := scalarObjective_min_lower ν hi hβ0 hβ1
  have hc := native_cvar_eq_objective P f x (hf_meas x) (hf_int x hx) β hβ0 hβ1
  have horder := (quantile_interval ν hβ0 hβ1).1
  have harg := scalarObjective_argmin ν hi hβ0 hβ1
  change lowerQuantile ν β = _ at hq
  change upperQuantile ν β = _ at hr
  change CVaR P f β x = scalarObjective ν β (lowerQuantile ν β) at hc
  rw [he, hq] at hm hc
  rw [he, hq, hr] at harg
  rw [hq, hr] at horder
  refine ⟨?_, ?_, ?_, ?_, ⟨horder, harg⟩, hm, hc⟩
  · intro a
    exact ((hf_int x hx).sub (integrable_const a)).sup (integrable_const 0)
  · rw [← he]
    exact scalarObjective_convex ν hi hβ1
  · rw [← he]
    exact scalarObjective_continuous ν hi hβ1
  · refine ⟨⟨VaR P f β x, hc.symm⟩, ?_⟩
    rintro y ⟨a, rfl⟩
    rw [hc]
    exact hm (Set.mem_univ a)

end CVaRProof


open MeasureTheory Filter Topology RUCVaR.MinFormula

namespace RUCVaR.MinFormula

/-- Theorem 10 (fundamental minimization formula), p. 14, (28)–(30). -/
theorem theorem_10 {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hx : x ∈ X) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) ∧ Continuous (Fbeta P f β x) ∧
    IsLeast (Set.range (Fbeta P f β x)) (CVaR P f β x) ∧
    (VaR P f β x ≤ VaRPlus P f β x ∧
      {α : ℝ | IsMinOn (Fbeta P f β x) Set.univ α} = Set.Icc (VaR P f β x) (VaRPlus P f β x)) ∧
    (IsMinOn (Fbeta P f β x) Set.univ (VaR P f β x) ∧
      CVaR P f β x = Fbeta P f β x (VaR P f β x)) := by
  exact CVaRProof.full_native_result P X f hf_cont hf_meas hf_int β hβ0 hβ1 x hx

end RUCVaR.MinFormula

open MeasureTheory Filter Topology RUCVaR.MinFormula

theorem solution {m n : ℕ} (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hf_cont : ∀ y, ContinuousOn (fun x => f x y) X) (hf_meas : ∀ x, Measurable (f x))
    (hf_int : ∀ x ∈ X, Integrable (f x) P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (x : Fin n → ℝ) (hx : x ∈ X) :
    (∀ α : ℝ, Integrable (fun y => max (f x y - α) 0) P) ∧
    ConvexOn ℝ Set.univ (Fbeta P f β x) ∧ Continuous (Fbeta P f β x) ∧
    IsLeast (Set.range (Fbeta P f β x)) (CVaR P f β x) ∧
    (VaR P f β x ≤ VaRPlus P f β x ∧
      {α : ℝ | IsMinOn (Fbeta P f β x) Set.univ α} = Set.Icc (VaR P f β x) (VaRPlus P f β x)) ∧
    (IsMinOn (Fbeta P f β x) Set.univ (VaR P f β x) ∧
      CVaR P f β x = Fbeta P f β x (VaR P f β x)) := RUCVaR.MinFormula.theorem_10 P X f hf_cont hf_meas hf_int β hβ0 hβ1 x hx
