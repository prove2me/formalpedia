-- Prove2me | solution 1 for RetailVariety.Statics.lhs13_increasing_in_p
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:06:56.967994+00:00
-- url     : https://prove2.me/submissions/68309928-f890-493d-8c20-749035dc3f0d

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology


namespace RetailVariety.Statics
open MeasureTheory ProbabilityTheory

noncomputable def phiN (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)

noncomputable def PhiN (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

lemma phiN_eq (x : ℝ) : gaussianPDFReal 0 1 x = phiN x := by
  simp [gaussianPDFReal_def, phiN]

lemma phiN_pos (x : ℝ) : 0 < phiN x := by
  unfold phiN; positivity

lemma continuous_phiN : Continuous phiN := by
  unfold phiN; fun_prop

lemma PhiN_sub (a b : ℝ) (hab : a ≤ b) : PhiN b - PhiN a = ∫ x in a..b, phiN x := by
  unfold PhiN
  have h1 : ENNReal.ofReal (cdf (gaussianReal 0 1) b)
      = ENNReal.ofReal (cdf (gaussianReal 0 1) a) + ENNReal.ofReal (∫ x in Set.Ioc a b, phiN x) := by
    have hI : gaussianReal 0 1 (Set.Ioc a b) = ENNReal.ofReal (∫ x in Set.Ioc a b, phiN x) := by
      rw [gaussianReal_apply_eq_integral 0 one_ne_zero]
      simp only [phiN_eq]
    rw [ofReal_cdf, ofReal_cdf, ← Set.Iic_union_Ioc_eq_Iic hab,
      measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, hI]
  have h2 : 0 ≤ ∫ x in Set.Ioc a b, phiN x :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => (phiN_pos x).le)
  rw [← ENNReal.ofReal_add (cdf_nonneg _ _) h2] at h1
  have := (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) (by have := cdf_nonneg (gaussianReal 0 1) a; linarith)).mp h1
  rw [intervalIntegral.integral_of_le hab]
  linarith

lemma PhiN_eq (x : ℝ) : PhiN x = PhiN 0 + ∫ t in (0:ℝ)..x, phiN t := by
  rcases le_total 0 x with h | h
  · have := PhiN_sub 0 x h; linarith
  · have := PhiN_sub x 0 h
    rw [intervalIntegral.integral_symm]; linarith

lemma PhiN_hasDerivAt (x : ℝ) : HasDerivAt PhiN (phiN x) x := by
  have h := (continuous_phiN.integral_hasStrictDerivAt 0 x).hasDerivAt
  have : PhiN = fun y => PhiN 0 + ∫ t in (0:ℝ)..y, phiN t := funext PhiN_eq
  rw [this]
  exact h.const_add _

lemma PhiN_continuous : Continuous PhiN := continuous_iff_continuousAt.2 fun x => (PhiN_hasDerivAt x).continuousAt

lemma PhiN_strictMono : StrictMono PhiN :=
  strictMono_of_deriv_pos (fun x => by rw [(PhiN_hasDerivAt x).deriv]; exact phiN_pos x)

lemma PhiN_mono : Monotone PhiN := PhiN_strictMono.monotone

lemma PhiN_le_one (x : ℝ) : PhiN x ≤ 1 := cdf_le_one _ _
lemma PhiN_nonneg (x : ℝ) : 0 ≤ PhiN x := cdf_nonneg _ _
lemma PhiN_atTop : Tendsto PhiN atTop (𝓝 1) := tendsto_cdf_atTop _
lemma PhiN_atBot : Tendsto PhiN atBot (𝓝 0) := tendsto_cdf_atBot _


lemma cf_spec {p c : ℝ} (hc : 0 < c) (hcp : c < p) :
    PhiN (criticalFractile p c) = 1 - c / p := by
  have hp : 0 < p := hc.trans hcp
  have hu0 : 0 < 1 - c / p := by have : c / p < 1 := (div_lt_one hp).2 hcp; linarith
  have hu1 : 1 - c / p < 1 := by have : 0 < c / p := div_pos hc hp; linarith
  obtain ⟨a, ha⟩ := (PhiN_atBot.eventually (gt_mem_nhds hu0)).exists
  obtain ⟨b, hb⟩ := (PhiN_atTop.eventually (lt_mem_nhds hu1)).exists
  have hab : a ≤ b := by
    by_contra h
    push_neg at h
    have := PhiN_mono h.le
    linarith
  obtain ⟨x0, -, hx0⟩ := intermediate_value_Icc hab PhiN_continuous.continuousOn
    ⟨ha.le, hb.le⟩
  have hT : {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x} = Set.Ici x0 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    change 1 - c / p ≤ PhiN x ↔ x0 ≤ x
    rw [← hx0]
    rw [PhiN_strictMono.le_iff_le]
  have hT' : criticalFractile p c = x0 := by
    show sInf {x : ℝ | 1 - c / p ≤ cdf (gaussianReal 0 1) x} = x0
    rw [hT, csInf_Ici]
  rw [hT']
  exact hx0

lemma cf_strictMonoOn {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) := by
  intro p1 h1 p2 h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  have e1 := cf_spec hc h1
  have e2 := cf_spec hc h2
  have hp1 : 0 < p1 := hc.trans h1
  have : 1 - c / p1 < 1 - c / p2 := by
    have : c / p2 < c / p1 := div_lt_div_of_pos_left hc hp1 h12
    linarith
  rw [← e1, ← e2] at this
  exact PhiN_strictMono.lt_iff_lt.1 this

lemma cf_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun p : ℝ => criticalFractile p c) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hM : PhiN M < 1 := lt_of_lt_of_le (PhiN_strictMono (lt_add_one M)) (PhiN_le_one _)
  have h1 : ∀ᶠ p : ℝ in atTop, c / p < 1 - PhiN M :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, eventually_gt_atTop c] with p hp hcp
  have := cf_spec hc hcp
  have h3 : PhiN M < PhiN (criticalFractile p c) := by rw [this]; linarith
  exact (PhiN_strictMono.lt_iff_lt.1 h3).le

lemma phiN_hasDerivAt (x : ℝ) : HasDerivAt phiN (-x * phiN x) x := by
  unfold phiN
  have h1 : HasDerivAt (fun x : ℝ => -x ^ 2 / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    refine this.congr_deriv ?_
    ring
  have := (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine this.congr_deriv ?_
  ring

lemma phiN_tendsto_atBot : Tendsto phiN atBot (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => Real.exp (y / 2)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.atBot_div_const (by norm_num : (0:ℝ) < 2))
  have h2 : Tendsto (fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (y / 2)) atBot (𝓝 0) := by
    simpa using h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine squeeze_zero' (Eventually.of_forall (fun y => (phiN_pos y).le)) ?_ h2
  filter_upwards [eventually_le_atBot (-1)] with y hy
  unfold phiN
  gcongr
  nlinarith


noncomputable def Mfun (z : ℝ) : ℝ := phiN z / (-z) - PhiN z

lemma Mfun_hasDerivAt {z : ℝ} (hz : z < 0) : HasDerivAt Mfun (phiN z / z ^ 2) z := by
  have hz0 : z ≠ 0 := hz.ne
  have h1 := (phiN_hasDerivAt z).div (hasDerivAt_id z).neg (by simpa using hz0)
  have h2 := h1.sub (PhiN_hasDerivAt z)
  refine h2.congr_deriv ?_
  simp only [Pi.neg_apply, id]
  field_simp
  ring

lemma Mfun_strictMonoOn : StrictMonoOn Mfun (Set.Iio 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Iio 0)
    (fun x hx => (Mfun_hasDerivAt hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Iio] at hx
  have hx' : x < 0 := hx
  rw [(Mfun_hasDerivAt hx').deriv]
  exact div_pos (phiN_pos x) (by have : x ≠ 0 := hx'.ne; positivity)

lemma Mfun_tendsto : Tendsto Mfun atBot (𝓝 0) := by
  have h1 : Tendsto (fun z => phiN z / (-z)) atBot (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ phiN_tendsto_atBot
    · filter_upwards [eventually_lt_atBot 0] with z hz
      exact div_nonneg (phiN_pos z).le (by linarith)
    · filter_upwards [eventually_le_atBot (-1)] with z hz
      rw [div_le_iff₀ (by linarith)]
      have := phiN_pos z
      nlinarith
  have := h1.sub PhiN_atBot
  have e : Mfun = fun z => phiN z / (-z) - PhiN z := rfl
  rw [e]
  simpa using this

lemma Mfun_pos {z : ℝ} (hz : z < 0) : 0 < Mfun z := by
  have h1 : 0 ≤ Mfun (z - 1) := by
    refine le_of_tendsto Mfun_tendsto ?_
    filter_upwards [eventually_le_atBot (z - 1)] with y hy
    rcases hy.lt_or_eq with h | h
    · exact (Mfun_strictMonoOn (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio]; linarith) h).le
    · rw [h]
  have h2 : Mfun (z - 1) < Mfun z :=
    Mfun_strictMonoOn (by simp only [Set.mem_Iio]; linarith) hz (by linarith)
  linarith

lemma H_pos (z : ℝ) : 0 < phiN z + z * PhiN z := by
  rcases le_or_gt 0 z with h | h
  · have := phiN_pos z
    have := mul_nonneg h (PhiN_nonneg z)
    linarith
  · have h1 := Mfun_pos h
    have hz0 : z ≠ 0 := h.ne
    have : phiN z + z * PhiN z = (-z) * Mfun z := by
      unfold Mfun
      field_simp
      ring
    rw [this]
    exact mul_pos (by linarith) h1

noncomputable def Gfun (z : ℝ) : ℝ := PhiN z * Real.exp (z ^ 2 / 2)

lemma Gfun_strictMono : StrictMono Gfun := by
  have hd : ∀ z, HasDerivAt Gfun (Real.exp (z ^ 2 / 2) * (phiN z + z * PhiN z)) z := by
    intro z
    have h1 := ((hasDerivAt_pow 2 z).div_const 2).exp
    have h2 := (PhiN_hasDerivAt z).mul h1
    refine h2.congr_deriv ?_
    push_cast
    ring
  refine strictMono_of_deriv_pos (fun z => ?_)
  rw [(hd z).deriv]
  exact mul_pos (Real.exp_pos _) (H_pos z)


theorem lhs13_core (c lam σ β : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) ∧
      StrictMonoOn (fun p : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
          * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi c) := by
  refine ⟨cf_strictMonoOn hc, ?_⟩
  have hK : 0 < Real.sqrt (2 * Real.pi) / σ * lam ^ (1 - β) := by positivity
  have hf : ∀ p ∈ Set.Ioi c, (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
          * Real.exp (criticalFractile p c ^ 2 / 2)
        = (Real.sqrt (2 * Real.pi) / σ * lam ^ (1 - β)) * Gfun (criticalFractile p c) := by
    intro p hp
    simp only [Set.mem_Ioi] at hp
    unfold Gfun
    rw [cf_spec hc hp]
    ring
  intro p1 h1 p2 h2 h12
  simp only
  rw [hf p1 h1, hf p2 h2]
  exact mul_lt_mul_of_pos_left (Gfun_strictMono (cf_strictMonoOn hc h1 h2 h12)) hK

end RetailVariety.Statics

open RetailVariety.Statics


theorem solution (c lam σ β : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) ∧
      StrictMonoOn (fun p : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
          * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi c) := by
  exact lhs13_core c lam σ β hc hlam hσ
