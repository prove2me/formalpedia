-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.corollary4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:28:09.314067+00:00
-- url     : https://prove2.me/submissions/338888b3-7ba3-4932-9965-7bf60d0fcb3a

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace XGT1

open XinGoldbergTBS.Asymptotic

lemma not_ae_ge (μ : DemandLaw) : ¬ (∀ᵐ x ∂μ.law, μ.mean ≤ x) := by
  intro h
  have hint : Integrable (fun x : ℝ => x - μ.mean) μ.law :=
    (μ.integrable.sub (integrable_const _))
  have h0 : ∫ x, (x - μ.mean) ∂μ.law = 0 := by
    have hI : Integrable (fun x : ℝ => x) μ.law := μ.integrable
    rw [integral_sub hI (integrable_const _)]
    simp [DemandLaw.mean]
  have hnn : 0 ≤ᵐ[μ.law] (fun x : ℝ => x - μ.mean) := by
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply]; linarith
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  have hae : ∀ᵐ x ∂μ.law, x ∈ ({μ.mean} : Set ℝ) := by
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    simp only [Set.mem_singleton_iff]; linarith
  have h1 : μ.law ({μ.mean} : Set ℝ)ᶜ = 0 := by
    rw [ae_iff] at hae
    simpa [Set.compl_def] using hae
  rw [prob_compl_eq_zero_iff (measurableSet_singleton _)] at h1
  exact (lt_irrefl _ (h1 ▸ μ.nondegenerate μ.mean))

lemma not_ae_le (μ : DemandLaw) : ¬ (∀ᵐ x ∂μ.law, x ≤ μ.mean) := by
  intro h
  have hint : Integrable (fun x : ℝ => μ.mean - x) μ.law :=
    ((integrable_const _).sub μ.integrable)
  have h0 : ∫ x, (μ.mean - x) ∂μ.law = 0 := by
    have hI : Integrable (fun x : ℝ => x) μ.law := μ.integrable
    rw [integral_sub (integrable_const _) hI]
    simp [DemandLaw.mean]
  have hnn : 0 ≤ᵐ[μ.law] (fun x : ℝ => μ.mean - x) := by
    filter_upwards [h] with x hx
    simp only [Pi.zero_apply]; linarith
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  have hae : ∀ᵐ x ∂μ.law, x ∈ ({μ.mean} : Set ℝ) := by
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    simp only [Set.mem_singleton_iff]; linarith
  have h1 : μ.law ({μ.mean} : Set ℝ)ᶜ = 0 := by
    rw [ae_iff] at hae
    simpa [Set.compl_def] using hae
  rw [prob_compl_eq_zero_iff (measurableSet_singleton _)] at h1
  exact (lt_irrefl _ (h1 ▸ μ.nondegenerate μ.mean))

lemma Iio_ne_zero (μ : DemandLaw) : μ.law (Set.Iio μ.mean) ≠ 0 := by
  intro h
  apply not_ae_ge μ
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx
  simpa using hx

lemma Ici_ne_zero (μ : DemandLaw) : μ.law (Set.Ici μ.mean) ≠ 0 := by
  intro h
  apply not_ae_le μ
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with x hx
  simp at hx; exact hx.le

lemma p0_pos (μ : DemandLaw) : 0 < p0 μ :=
  ENNReal.toReal_pos (Iio_ne_zero μ) (measure_ne_top _ _)

lemma p0_lt_one (μ : DemandLaw) : p0 μ < 1 := by
  have hlt : μ.law (Set.Iio μ.mean) < 1 := by
    refine lt_of_le_of_ne prob_le_one ?_
    intro h1
    rw [← prob_compl_eq_zero_iff measurableSet_Iio, Set.compl_Iio] at h1
    exact Ici_ne_zero μ h1
  have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr hlt
  simpa [p0] using this

lemma mean_pos (μ : DemandLaw) : 0 < μ.mean := by
  by_contra hle
  push Not at hle
  apply Iio_ne_zero μ
  exact measure_mono_null (Set.Iio_subset_Iio hle) μ.nonneg

/-- some point `a < mean` with `P(D ≤ a) > p0/2`. -/
lemma exists_left (μ : DemandLaw) :
    ∃ a : ℝ, a < μ.mean ∧ ENNReal.ofReal (p0 μ / 2) < μ.law (Set.Iic a) := by
  set m := μ.mean
  have hU : Set.Iio m = ⋃ n : ℕ, Set.Iic (m - 1 / ((n : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun n : ℕ => Set.Iic (m - 1 / ((n : ℝ) + 1))) := by
    intro i j hij
    apply Set.Iic_subset_Iic.mpr
    have : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := Nat.one_div_le_one_div hij
    linarith
  have hsup : μ.law (Set.Iio m) = ⨆ n : ℕ, μ.law (Set.Iic (m - 1 / ((n : ℝ) + 1))) := by
    rw [hU]; exact hmono.measure_iUnion
  have hlt : ENNReal.ofReal (p0 μ / 2) < μ.law (Set.Iio m) := by
    have hp := p0_pos μ
    have : μ.law (Set.Iio m) = ENNReal.ofReal (p0 μ) := by
      simp [p0, m, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact (ENNReal.ofReal_lt_ofReal_iff hp).mpr (by linarith)
  rw [hsup, lt_iSup_iff] at hlt
  obtain ⟨n, hn⟩ := hlt
  refine ⟨m - 1 / ((n : ℝ) + 1), ?_, hn⟩
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma Q0_lt_mean (μ : DemandLaw) : Q0 μ < μ.mean := by
  obtain ⟨a, ha, hP⟩ := exists_left μ
  have hm := mean_pos μ
  set x := max a 0
  have hx : x < μ.mean := max_lt ha hm
  have hmem : x ∈ {x : ℝ | 0 ≤ x ∧ (1 / 2) * p0 μ ≤ (μ.law (Set.Iic x)).toReal} := by
    refine ⟨le_max_right _ _, ?_⟩
    have h1 : μ.law (Set.Iic a) ≤ μ.law (Set.Iic x) :=
      measure_mono (Set.Iic_subset_Iic.mpr (le_max_left _ _))
    have h2 := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp (hP.le.trans h1)
    linarith
  have : Q0 μ ≤ x := csInf_le ⟨0, fun y hy => hy.1⟩ hmem
  linarith

lemma eta0_pos (μ : DemandLaw) : 0 < eta0 μ := by
  obtain ⟨a, ha, hP⟩ := exists_left μ
  set m := μ.mean
  have hA : 0 < μ.law.real (Set.Iic a) :=
    ENNReal.toReal_pos (fun h0 => by simp [h0] at hP) (measure_ne_top _ _)
  have hB : 0 < μ.law.real (Set.Ici m) :=
    ENNReal.toReal_pos (Ici_ne_zero μ) (measure_ne_top _ _)
  set q := min (μ.law.real (Set.Iic a)) (μ.law.real (Set.Ici m))
  have hq : 0 < q := lt_min hA hB
  have hd : 0 < (m - a) / 2 := by linarith
  have key : ∀ z : ℝ, (m - a) / 2 * q ≤ ∫ d, |z - d| ∂μ.law := by
    intro z
    have hint : Integrable (fun d : ℝ => |z - d|) μ.law :=
      ((integrable_const z).sub μ.integrable).abs
    have hnn : 0 ≤ᵐ[μ.law] (fun d : ℝ => |z - d|) :=
      Eventually.of_forall (fun d => abs_nonneg _)
    have hM := mul_meas_ge_le_integral_of_nonneg hnn hint ((m - a) / 2)
    refine le_trans ?_ hM
    apply mul_le_mul_of_nonneg_left _ hd.le
    rcases le_or_gt ((a + m) / 2) z with hz | hz
    · refine (min_le_left _ _).trans (measureReal_mono ?_)
      intro d hd'
      simp only [Set.mem_Iic] at hd'
      simp only [Set.mem_setOf_eq]
      rw [abs_of_nonneg (by linarith)]; linarith
    · refine (min_le_right _ _).trans (measureReal_mono ?_)
      intro d hd'
      simp only [Set.mem_Ici] at hd'
      simp only [Set.mem_setOf_eq]
      rw [abs_of_neg (by linarith)]; linarith
  exact lt_of_lt_of_le (mul_pos hd hq) (le_ciInf key)

lemma eps0_pos (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : 0 < eps0 μ κ L₀ := by
  have hp := p0_pos μ
  have hp1 := p0_lt_one μ
  have hph : 0 < p0hat μ := Real.sqrt_pos.mpr (by nlinarith)
  have hη := eta0_pos μ
  have hm := mean_pos μ
  have hQ := Q0_lt_mean μ
  have hU : 0 ≤ UConst μ κ L₀ := by
    unfold UConst
    have h1 : 0 ≤ κ.c * μ.mean := mul_nonneg κ.c_pos.le hm.le
    have h2 : 0 ≤ ∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀ := by
      apply integral_nonneg
      intro y
      unfold G
      have := κ.h_pos; have := κ.b_pos
      positivity
    linarith
  have hU0 : 0 ≤ U0 μ κ L₀ := by
    unfold U0
    have hb := κ.b_pos; have hh := κ.h_pos
    have hmin : 0 < min κ.b κ.h := lt_min hb hh
    positivity
  have hc0 : 0 < c0 μ κ := by
    unfold c0
    have hmin : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
    positivity
  have hS : 0 < U0 μ κ L₀ * 2 ^ L₀ + eta0 μ + UConst μ κ L₀ + 1 := by positivity
  unfold eps0
  refine lt_min (by linarith) (lt_min (by positivity) (lt_min ?_ (by positivity)))
  have : (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      have : 0 < p0hat μ ^ 2 := by positivity
      linarith [show -(p0hat μ ^ 2) / 400 = -(p0hat μ ^ 2 / 400) by ring])
  linarith

lemma two_rpow_neg_ge (y : ℝ) (hy : 0 ≤ y) : 1 - y ≤ (2 : ℝ) ^ (-y) := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h1 := Real.add_one_le_exp (Real.log 2 * -y)
  have hl := Real.log_two_lt_d9
  nlinarith

lemma p0hat_facts (μ : DemandLaw) : 0 < p0hat μ ∧ p0hat μ ^ 2 ≤ 1 / 8 := by
  have hp := p0_pos μ
  have hp1 := p0_lt_one μ
  have hph2 : p0hat μ ^ 2 = p0 μ * (1 - p0 μ) / 2 := by
    rw [p0hat, Real.sq_sqrt (by nlinarith)]; ring
  exact ⟨Real.sqrt_pos.mpr (by nlinarith), by rw [hph2]; nlinarith [sq_nonneg (p0 μ - 1 / 2)]⟩

lemma eps0_le_small (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : eps0 μ κ L₀ ≤ 1 / 3200 := by
  obtain ⟨hph, hph8⟩ := p0hat_facts μ
  have heB : eps0 μ κ L₀ ≤ 1 - (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400) := by
    unfold eps0; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlow : 1 - p0hat μ ^ 2 / 400 ≤ (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400) := by
    rw [neg_div]; exact two_rpow_neg_ge _ (by positivity)
  linarith

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  positivity

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_lip (κ : Costs) (a c : ℝ) : G κ a ≤ G κ c + max κ.b κ.h * |a - c| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  have hbp := κ.b_pos
  have hhp := κ.h_pos
  have h1 := le_abs_self (a - c)
  have h2 := neg_abs_le (a - c)
  have h3 := abs_nonneg (a - c)
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 c with hc | hc
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

instance sumLaw_isProb (μ : DemandLaw) (L₀ : ℕ) : IsProbabilityMeasure (sumLaw μ L₀) := by
  unfold sumLaw; infer_instance

end XGT1

namespace XGOB

open XinGoldbergTBS.Asymptotic

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma G_nonneg (κ : Costs) (z : ℝ) : 0 ≤ G κ z := by
  unfold G
  have := κ.h_pos; have := κ.b_pos
  positivity

lemma G_ge (κ : Costs) (z : ℝ) : min κ.b κ.h * |z| ≤ G κ z := by
  unfold G
  have hb := min_le_left κ.b κ.h
  have hh := min_le_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_lip (κ : Costs) (a c : ℝ) : G κ a ≤ G κ c + max κ.b κ.h * |a - c| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  have hbp := κ.b_pos
  have hhp := κ.h_pos
  have h1 := le_abs_self (a - c)
  have h2 := neg_abs_le (a - c)
  have h3 := abs_nonneg (a - c)
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 c with hc | hc
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_left ha, max_eq_right (by linarith : -a ≤ 0), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_left hc,
      max_eq_right (by linarith : -c ≤ 0)]
    nlinarith
  · rw [max_eq_right ha, max_eq_left (by linarith : 0 ≤ -a), max_eq_right hc,
      max_eq_left (by linarith : 0 ≤ -c)]
    nlinarith

lemma continuous_G (κ : Costs) : Continuous (G κ) := by
  unfold G
  exact (continuous_const.mul (continuous_id.max continuous_const)).add
    (continuous_const.mul (continuous_neg.max continuous_const))

instance sumLaw_isProb (μ : DemandLaw) (L₀ : ℕ) : IsProbabilityMeasure (sumLaw μ L₀) := by
  unfold sumLaw; infer_instance

lemma integrable_coord (μ : DemandLaw) (L₀ : ℕ) (i : Fin (L₀ + 1)) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => y i) (sumLaw μ L₀) := by
  unfold sumLaw
  exact integrable_comp_eval (μ := fun _ : Fin (L₀ + 1) => μ.law) (f := fun d : ℝ => d) μ.integrable

lemma integrable_shift (μ : DemandLaw) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => x - ∑ i, y i) (sumLaw μ L₀) :=
  (integrable_const x).sub (integrable_finsetSum _ fun i _ => integrable_coord μ L₀ i)

lemma integrable_G_sum (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (x : ℝ) :
    Integrable (fun y : Fin (L₀ + 1) → ℝ => G κ (x - ∑ i, y i)) (sumLaw μ L₀) := by
  have hs := integrable_shift μ L₀ x
  refine Integrable.mono' (hs.norm.const_mul (max κ.b κ.h)) ?_ ?_
  · exact ((continuous_G κ).measurable.comp_aemeasurable hs.aemeasurable).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (G_nonneg _ _), Real.norm_eq_abs]
      exact G_le κ _

instance ghat_isProb : IsProbabilityMeasure ghatLaw := by
  constructor
  unfold ghatLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ = 2⁻¹ * (2⁻¹) ^ i := by
    intro i; rw [ENNReal.inv_pow, pow_succ, mul_comm]
  calc _ = ∑' i : ℕ, ((2 : ℝ≥0∞) ^ (i + 1))⁻¹ := by simp
    _ = 1 := by
      simp only [h]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
        ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

instance sampleLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (sampleLaw μ) := by
  unfold sampleLaw; infer_instance

lemma measurable_initState : Measurable (fun ω : Sample => initState ω) := by
  unfold initState
  refine measurable_const.prodMk (measurable_const.prodMk ?_)
  have : Measurable (fun q : Path × ℕ => -∑ i ∈ Finset.range q.2, q.1 i) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).neg
  exact this.comp measurable_snd

lemma measurable_step (L₀ L t : ℕ) :
    Measurable (fun q : (ℝ≥0 × ℝ≥0) × ℝ × State => step L₀ L t q.1 q.2.1 q.2.2) := by
  unfold step; fun_prop

lemma measurable_observe (L₀ L t : ℕ) : Measurable (observe L₀ L t) := by
  unfold observe; fun_prop

lemma measurable_run {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (n : ℕ) :
    Measurable (fun ω : Sample => run π ω n) := by
  induction n with
  | zero => exact measurable_initState
  | succ n ih =>
    have h1 : Measurable (fun ω : Sample => π.f (n + 1) (observe L₀ L (n + 1) (run π ω n))) :=
      (π.measurable_f _).comp ((measurable_observe _ _ _).comp ih)
    have h2 : Measurable (fun ω : Sample => ω.1 n) := (measurable_pi_apply n).comp measurable_fst
    exact (measurable_step L₀ L (n + 1)).comp (h1.prodMk (h2.prodMk ih))

/-- Replace the coordinates `m ≤ n < m + k` of `p` by those of `y`. -/
def mix (m k : ℕ) (p y : Path) : Path := fun n => if m ≤ n ∧ n < m + k then y n else p n

lemma measurable_mix (m k : ℕ) : Measurable (fun q : Path × Path => mix m k q.1 q.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : m ≤ n ∧ n < m + k
  · simp only [mix, h, and_self, if_true]; fun_prop
  · simp only [mix, h, if_false]; fun_prop

lemma mp_mix (μ : DemandLaw) (m k : ℕ) :
    MeasurePreserving (fun q : Path × Path => mix m k q.1 q.2)
      ((pathLaw μ).prod (pathLaw μ)) (pathLaw μ) := by
  refine ⟨measurable_mix m k, ?_⟩
  conv_rhs => rw [pathLaw]
  apply Measure.eq_infinitePi
  intro s t ht
  classical
  rw [Measure.map_apply (measurable_mix m k) (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  have hpre : (fun q : Path × Path => mix m k q.1 q.2) ⁻¹' (Set.pi (↑s) t) =
      (Set.pi ↑(s.filter (fun i => ¬ (m ≤ i ∧ i < m + k))) t) ×ˢ
        (Set.pi ↑(s.filter (fun i => m ≤ i ∧ i < m + k)) t) := by
    ext ⟨p, y⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_coe, mix]
    constructor
    · intro h
      exact ⟨fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi,
        fun i ⟨hi, hw⟩ => by simpa [hw] using h i hi⟩
    · rintro ⟨h1, h2⟩ i hi
      by_cases hw : m ≤ i ∧ i < m + k
      · simpa [hw] using h2 i ⟨hi, hw⟩
      · simpa [hw] using h1 i ⟨hi, hw⟩
  rw [hpre, Measure.prod_prod]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun i _ => ht i), Measure.infinitePi_pi _ (fun i _ => ht i), mul_comm,
    Finset.prod_filter_mul_prod_filter_not]

lemma mp_window (μ : DemandLaw) (L₀ m : ℕ) :
    MeasurePreserving (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j))
      (pathLaw μ) (sumLaw μ L₀) := by
  refine ⟨by fun_prop, ?_⟩
  unfold sumLaw
  refine (Measure.pi_eq fun s hs => ?_).symm
  classical
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  set T : ℕ → Set ℝ := fun n =>
    if h : m ≤ n ∧ n < m + (L₀ + 1) then s ⟨n - m, by omega⟩ else Set.univ with hTdef
  have hT : ∀ j : Fin (L₀ + 1), T (m + j) = s j := by
    intro j
    simp only [hTdef]
    rw [dif_pos (by omega)]
    congr 1; ext; simp
  have hpre : (fun p : Path => fun j : Fin (L₀ + 1) => p (m + j)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image (fun j : Fin (L₀ + 1) => m + (j : ℕ))) T := by
    ext p
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_pi, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff, hT]
    exact ⟨fun h a => h a (Set.mem_univ _), fun h a _ => h a⟩
  have hTm : ∀ n, MeasurableSet (T n) := by
    intro n; simp only [hTdef]; split_ifs
    · exact hs _
    · exact MeasurableSet.univ
  rw [hpre]
  unfold pathLaw
  rw [Measure.infinitePi_pi _ (fun n _ => hTm n),
    Finset.prod_image (fun a _ b _ h => by ext; simpa using h)]
  exact Finset.prod_congr rfl fun j _ => by rw [hT j]

lemma lintegral_mix (μ : DemandLaw) (m k : ℕ) {f : Sample → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω ∂sampleLaw μ =
      ∫⁻ ω, ∫⁻ y, f (mix m k ω.1 y, ω.2) ∂pathLaw μ ∂sampleLaw μ := by
  have hg : Measurable (fun q : Sample × Path => f (mix m k q.1.1 q.2, q.1.2)) :=
    hf.comp (((measurable_mix m k).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)
  have hF : Measurable (fun p : Path => ∫⁻ r, f (p, r) ∂((pathLaw μ).prod ghatLaw)) :=
    hf.lintegral_prod_right'
  unfold sampleLaw
  have hFm : Measurable (fun a : Path × Path =>
      ∫⁻ r, f (mix m k a.1 a.2, r) ∂((pathLaw μ).prod ghatLaw)) := hF.comp (measurable_mix m k)
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.lintegral_prod_right'.aemeasurable,
    ← (mp_mix μ m k).lintegral_comp hF, lintegral_prod _ hFm.aemeasurable]
  refine lintegral_congr fun p => ?_
  simp only
  refine lintegral_lintegral_swap ?_
  exact (hf.comp (((measurable_mix m k).comp (measurable_const.prodMk measurable_fst)).prodMk
    measurable_snd)).aemeasurable

lemma run_local {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω ω' : Sample) (h2 : ω.2 = ω'.2)
    (m : ℕ) (h1 : ∀ n < m, ω.1 n = ω'.1 n) : ∀ j ≤ m, run π ω j = run π ω' j := by
  intro j hj
  induction j with
  | zero => simp only [run, initState, h2]
  | succ j ih => simp only [run]; rw [ih (by omega), h1 j (by omega)]

lemma run_shift {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (hL : L₀ ≤ L) (hL1 : 1 ≤ L)
    (ω ω' : Sample) (h2 : ω.2 = ω'.2)
    (m : ℕ) (h1 : ∀ n < m, ω.1 n = ω'.1 n) (n : ℕ) (hn1 : m + 1 ≤ n) (hn2 : n ≤ m + L₀ + 1) :
    (∀ i : ℤ, i ≤ (m : ℤ) + 1 →
        (run π ω n).1 i = (run π ω' n).1 i ∧ (run π ω n).2.1 i = (run π ω' n).2.1 i) ∧
      (run π ω n).2.2 + ∑ k ∈ Finset.range n, ω.1 k =
        (run π ω' n).2.2 + ∑ k ∈ Finset.range n, ω'.1 k := by
  induction n, hn1 using Nat.le_induction with
  | base =>
    have hm := run_local π ω ω' h2 m h1 m le_rfl
    simp only [run]
    rw [hm]
    refine ⟨fun i _ => ⟨rfl, rfl⟩, ?_⟩
    simp only [step, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl (fun k hk => h1 k (Finset.mem_range.1 hk))]
    ring
  | succ n hn ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [run]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hne : i ≠ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [step, Function.update_apply, hne, if_false]
      exact ih1 i hi
    · have hR : ((n + 1 : ℕ) : ℤ) - L ≠ ((n + 1 : ℕ) : ℤ) := by omega
      have hE : ((n + 1 : ℕ) : ℤ) - L₀ ≠ ((n + 1 : ℕ) : ℤ) := by omega
      simp only [step, Function.update_apply, Finset.sum_range_succ, hR, hE, if_false]
      have e1 := (ih1 (((n + 1 : ℕ) : ℤ) - L) (by omega)).1
      have e2 := (ih1 (((n + 1 : ℕ) : ℤ) - L₀) (by omega)).2
      rw [e1, e2]
      linarith

lemma run_mix_inv {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (hL : L₀ ≤ L) (hL1 : 1 ≤ L)
    (ω : Sample) (y : Path) (m : ℕ) :
    (run π (mix m (L₀ + 1) ω.1 y, ω.2) (m + L₀ + 1)).2.2 =
      (run π ω (m + L₀ + 1)).2.2 + ∑ j : Fin (L₀ + 1), ω.1 (m + j)
        - ∑ j : Fin (L₀ + 1), y (m + j) := by
  have h1 : ∀ n < m, ω.1 n = (mix m (L₀ + 1) ω.1 y, ω.2).1 n := by
    intro n hn; simp only [mix]; rw [if_neg (by omega)]
  obtain ⟨-, h⟩ := run_shift π hL hL1 ω (mix m (L₀ + 1) ω.1 y, ω.2) rfl m h1 (m + L₀ + 1)
    (by omega) le_rfl
  rw [show m + L₀ + 1 = m + (L₀ + 1) by ring, Finset.sum_range_add _ m (L₀ + 1),
    Finset.sum_range_add _ m (L₀ + 1)] at h
  rw [Finset.sum_congr rfl (fun k hk => (h1 k (Finset.mem_range.1 hk)).symm)] at h
  have h3 : ∑ x ∈ Finset.range (L₀ + 1), (mix m (L₀ + 1) ω.1 y, ω.2).1 (m + x) =
      ∑ x ∈ Finset.range (L₀ + 1), y (m + x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.mem_range.1 hx
    simp only [mix]; rw [if_pos (by omega)]
  rw [h3] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => ω.1 (m + j)), Fin.sum_univ_eq_sum_range (fun j => y (m + j))]
  rw [show m + (L₀ + 1) = m + L₀ + 1 by ring] at h
  linarith

lemma gConst_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (x : ℝ) :
    gConst μ κ L₀ ≤ ∫ y, G κ (x - ∑ i, y i) ∂sumLaw μ L₀ := by
  refine ciInf_le ⟨0, ?_⟩ x
  rintro _ ⟨z, rfl⟩
  exact integral_nonneg fun _ => G_nonneg _ _

lemma period_lower (μ : DemandLaw) (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L)
    (hL : L₀ ≤ L) (hL1 : 1 ≤ L) (t : ℕ) (ht : L₀ + 1 ≤ t) :
    ENNReal.ofReal (gConst μ κ L₀) ≤ ∫⁻ ω, periodCost κ π ω t ∂sampleLaw μ := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + L₀ + 1 := ⟨t - L₀ - 1, by omega⟩
  set F : Sample → ℝ≥0∞ := fun ω => ENNReal.ofReal (G κ (run π ω (m + L₀ + 1)).2.2) with hFdef
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
      (measurable_run π _).snd.snd)
  calc ENNReal.ofReal (gConst μ κ L₀)
      = ∫⁻ _ω, ENNReal.ofReal (gConst μ κ L₀) ∂sampleLaw μ := by simp
    _ ≤ ∫⁻ ω, ∫⁻ y, F (mix m (L₀ + 1) ω.1 y, ω.2) ∂pathLaw μ ∂sampleLaw μ := by
        refine lintegral_mono fun ω => ?_
        set X := (run π ω (m + L₀ + 1)).2.2 + ∑ j : Fin (L₀ + 1), ω.1 (m + j)
        have hrw : ∀ y, F (mix m (L₀ + 1) ω.1 y, ω.2) =
            (fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (X - ∑ i, z i)))
              (fun j : Fin (L₀ + 1) => y (m + j)) := by
          intro y; simp only [hFdef]; rw [run_mix_inv π hL hL1 ω y m]
        simp only [hrw]
        have hcomp := (mp_window μ L₀ m).lintegral_comp
          (f := fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (X - ∑ i, z i)))
          (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
            (measurable_const.sub (by fun_prop))))
        simp only at hcomp
        rw [hcomp]
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_G_sum μ κ L₀ X)
          (Eventually.of_forall fun _ => G_nonneg _ _)]
        exact ENNReal.ofReal_le_ofReal (gConst_le μ κ L₀ X)
    _ = ∫⁻ ω, F ω ∂sampleLaw μ := (lintegral_mix μ m (L₀ + 1) hF).symm
    _ ≤ _ := lintegral_mono fun ω => by
        simp only [hFdef, periodCost]; exact le_add_self

lemma tendsto_frac (a : ℝ≥0∞) (ha : a ≠ ⊤) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => ((T - L₀ : ℕ) : ℝ≥0∞) * a / T) atTop (𝓝 a) := by
  have e : ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal ((1 - (L₀ : ℝ) / T) * a.toReal) = ((T - L₀ : ℕ) : ℝ≥0∞) * a / T := by
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_natCast (T - L₀),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast T,
      ← ENNReal.ofReal_div_of_pos hT0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [Nat.cast_sub (by omega)]
    field_simp
  refine Tendsto.congr' e ?_
  have : Tendsto (fun T : ℕ => (1 - (L₀ : ℝ) / T) * a.toReal) atTop (𝓝 ((1 - 0) * a.toReal)) :=
    (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (L₀ : ℝ))).mul
      tendsto_const_nhds
  rw [sub_zero, one_mul] at this
  have h2 := ENNReal.tendsto_ofReal this
  rwa [ENNReal.ofReal_toReal ha] at h2

lemma policy_lower (μ : DemandLaw) (κ : Costs) {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L)
    (hL : L₀ ≤ L) (hL1 : 1 ≤ L) :
    ENNReal.ofReal (gConst μ κ L₀) ≤ policyCost μ κ π := by
  unfold policyCost
  refine le_trans (le_of_eq
    (tendsto_frac (ENNReal.ofReal (gConst μ κ L₀)) ENNReal.ofReal_ne_top L₀).limsup_eq.symm) ?_
  refine Filter.limsup_le_limsup (Eventually.of_forall fun T => ?_)
  refine ENNReal.div_le_div_right ?_ _
  calc ((T - L₀ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gConst μ κ L₀)
      = ∑ _t ∈ Finset.Icc (L₀ + 1) T, ENNReal.ofReal (gConst μ κ L₀) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show T + 1 - (L₀ + 1) = T - L₀ by omega]
    _ ≤ _ := Finset.sum_le_sum fun t ht =>
        period_lower μ κ π hL hL1 t (Finset.mem_Icc.1 ht).1

/-! ## The policy `π_{0,0}` -/

/-- Expedited position of a state whose regular pipeline is empty. -/
def EP (L₀ t : ℕ) (s : State) : ℝ := s.2.2 + ∑ i : Fin L₀, s.2.1 ((t : ℤ) - L₀ + ((i : ℕ) : ℤ))

lemma ep_eq (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) :
    expeditedPosition (observe L₀ L t s) = EP L₀ t s := by
  simp [expeditedPosition, observe, EP, hs]

lemma shift_sum (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    f a + ∑ i : Fin n, f (a + 1 + ((i : ℕ) : ℤ)) =
      ∑ i : Fin n, f (a + ((i : ℕ) : ℤ)) + f (a + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← add_assoc, ih]
    have e : a + 1 + (n : ℤ) = a + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]

lemma ep_step (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) (e : ℝ≥0) (d : ℝ) :
    (step L₀ L t (0, e) d s).1 = 0 ∧
      EP L₀ (t + 1) (step L₀ L t (0, e) d s) = EP L₀ t s + e - d := by
  have h0 : ∀ j, Function.update s.1 (t : ℤ) ((0 : ℝ≥0) : ℝ) j = 0 := by
    intro j; simp [hs, Function.update_apply]
  constructor
  · ext j; exact h0 j
  · simp only [EP, step]
    rw [h0]
    set f := Function.update s.2.1 (t : ℤ) (e : ℝ) with hf
    have hsh := shift_sum f ((t : ℤ) - L₀) L₀
    have hidx : ∀ i : Fin L₀, ((t + 1 : ℕ) : ℤ) - L₀ + ((i : ℕ) : ℤ) =
        (t : ℤ) - L₀ + 1 + ((i : ℕ) : ℤ) := by intro i; push_cast; ring
    simp only [hidx]
    have hlast : f ((t : ℤ) - L₀ + L₀) = e := by simp [hf]
    have hlow : ∀ i : Fin L₀, f ((t : ℤ) - L₀ + ((i : ℕ) : ℤ)) =
        s.2.1 ((t : ℤ) - L₀ + ((i : ℕ) : ℤ)) := by
      intro i; rw [hf, Function.update_of_ne]; have := i.isLt; omega
    rw [hlast] at hsh
    simp only [hlow] at hsh
    linarith

lemma tbs_f (L₀ L t : ℕ) (s : State) (hs : s.1 = 0) :
    (tbsPolicy L₀ L 0 0).f t (observe L₀ L t s) = (0, (-EP L₀ t s).toNNReal) := by
  show ((0 : ℝ).toNNReal, (0 - expeditedPosition (observe L₀ L t s)).toNNReal) = _
  rw [ep_eq L₀ L t s hs, Real.toNNReal_zero, zero_sub]

/-- The order quantity `q^E_{n+1}` of `π_{0,0}` (a.s.). -/
def v (ω : Sample) (n : ℕ) : ℝ :=
  if n = 0 then ∑ i ∈ Finset.range ω.2.2, ω.2.1 i else ω.1 (n - 1)

lemma v_nonneg (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (n : ℕ) : 0 ≤ v ω n := by
  unfold v; split_ifs
  · exact hS
  · exact hD _

lemma sim (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (n : ℕ) :
    (run (tbsPolicy L₀ L 0 0) ω n).1 = 0 ∧
      EP L₀ (n + 1) (run (tbsPolicy L₀ L 0 0) ω n) = - v ω n ∧
      run (tbsPolicy L₀ L 0 0) ω (n + 1) =
        step L₀ L (n + 1) (0, (v ω n).toNNReal) (ω.1 n) (run (tbsPolicy L₀ L 0 0) ω n) := by
  induction n with
  | zero =>
    have h1 : (run (tbsPolicy L₀ L 0 0) ω 0).1 = 0 := rfl
    have h2 : EP L₀ (0 + 1) (run (tbsPolicy L₀ L 0 0) ω 0) = - v ω 0 := by
      simp [run, initState, EP, v]
    refine ⟨h1, h2, ?_⟩
    simp only [run]
    simp only [run] at h1 h2
    rw [show (tbsPolicy L₀ L 0 0).f (0 + 1) (observe L₀ L (0 + 1) (initState ω)) =
      (0, (v ω 0).toNNReal) by simp only [tbsPolicy, ep_eq L₀ L _ _ h1, h2, Real.toNNReal_zero,
        zero_sub, neg_neg]]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨h4, h5⟩ := ep_step L₀ L (n + 1) _ h1 (v ω n).toNNReal (ω.1 n)
    have hv := v_nonneg ω hD hS n
    have hvs : v ω (n + 1) = ω.1 n := by simp [v]
    have g1 : (run (tbsPolicy L₀ L 0 0) ω (n + 1)).1 = 0 := by rw [h3]; exact h4
    have g2 : EP L₀ (n + 1 + 1) (run (tbsPolicy L₀ L 0 0) ω (n + 1)) = - v ω (n + 1) := by
      rw [h3, h5, h2, Real.coe_toNNReal _ hv, hvs]; ring
    refine ⟨g1, g2, ?_⟩
    conv_lhs => rw [run]
    rw [tbs_f L₀ L _ _ g1, g2, neg_neg]

lemma hist_stable {L₀ L : ℕ} (π : AdmissiblePolicy L₀ L) (ω : Sample) (i : ℤ) (n : ℕ)
    (hi : i ≤ n) (k : ℕ) : (run π ω (n + k)).2.1 i = (run π ω n).2.1 i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    have hne : i ≠ ((n + k + 1 : ℕ) : ℤ) := by omega
    show (run π ω (n + k + 1)).2.1 i = _
    simp only [run, step, Function.update_apply, hne, if_false]

lemma hist_val (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (j n : ℕ) (h : j + 1 ≤ n) :
    (run (tbsPolicy L₀ L 0 0) ω n).2.1 ((j + 1 : ℕ) : ℤ) = v ω j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [hist_stable _ ω _ (j + 1) le_rfl k, (sim L₀ L ω hD hS j).2.2]
  simp [step, Real.coe_toNNReal _ (v_nonneg ω hD hS j)]

lemma cost_formula (κ : Costs) (L₀ L : ℕ) (ω : Sample) (hD : ∀ n, 0 ≤ ω.1 n)
    (hS : 0 ≤ ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) (m : ℕ) :
    periodCost κ (tbsPolicy L₀ L 0 0) ω (m + L₀ + 1) =
      ENNReal.ofReal (κ.c * v ω m) +
        ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j))) := by
  unfold periodCost
  have hi1 : ((m + L₀ + 1 : ℕ) : ℤ) - L₀ = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hi1, hist_val L₀ L ω hD hS m _ (by omega)]
  congr 3
  obtain ⟨-, h2, -⟩ := sim L₀ L ω hD hS (m + L₀ + 1)
  simp only [EP] at h2
  have hidx : ∀ i : Fin L₀, ((m + L₀ + 1 + 1 : ℕ) : ℤ) - L₀ + ((i : ℕ) : ℤ) =
      ((m + 1 + i + 1 : ℕ) : ℤ) := by intro i; push_cast; ring
  simp only [hidx] at h2
  rw [Finset.sum_congr rfl (fun (i : Fin L₀) _ => hist_val L₀ L ω hD hS (m + 1 + i) (m + L₀ + 1)
    (by have := i.isLt; omega))] at h2
  have hv1 : ∀ i : Fin L₀, v ω (m + 1 + i) = ω.1 (m + i) := by
    intro i
    have h : m + 1 + (i : ℕ) ≠ 0 := by omega
    rw [v, if_neg h, show m + 1 + (i : ℕ) - 1 = m + i by omega]
  have hv2 : v ω (m + L₀ + 1) = ω.1 (m + L₀) := by simp [v]
  simp only [hv1, hv2] at h2
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last]
  linarith

lemma mp_fst (μ : DemandLaw) : MeasurePreserving Prod.fst (sampleLaw μ) (pathLaw μ) :=
  ⟨measurable_fst, by unfold sampleLaw; rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_snd (μ : DemandLaw) :
    MeasurePreserving Prod.snd (sampleLaw μ) ((pathLaw μ).prod ghatLaw) :=
  ⟨measurable_snd, by unfold sampleLaw; rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

lemma mp_fst' (μ : DemandLaw) :
    MeasurePreserving Prod.fst ((pathLaw μ).prod ghatLaw) (pathLaw μ) :=
  ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

lemma mp_eval (μ : DemandLaw) (n : ℕ) :
    MeasurePreserving (fun p : Path => p n) (pathLaw μ) μ.law := by
  unfold pathLaw; exact measurePreserving_eval_infinitePi _ n

lemma ae_good (μ : DemandLaw) :
    ∀ᵐ ω ∂sampleLaw μ, (∀ n, 0 ≤ ω.1 n) ∧ (∀ n, 0 ≤ ω.2.1 n) := by
  refine (ae_all_iff.2 fun n => ?_).and (ae_all_iff.2 fun n => ?_)
  · have hmp := (mp_eval μ n).comp (mp_fst μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)
  · have hmp := ((mp_eval μ n).comp (mp_fst' μ)).comp (mp_snd μ)
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)

lemma E_win (μ : DemandLaw) (κ : Costs) (L₀ m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j))) ∂sampleLaw μ =
      ENNReal.ofReal (∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀) := by
  have hmp := (mp_window μ L₀ m).comp (mp_fst μ)
  have hc := hmp.lintegral_comp
    (f := fun z : Fin (L₀ + 1) → ℝ => ENNReal.ofReal (G κ (-∑ i, z i)))
    (ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp (by fun_prop)))
  simp only [Function.comp] at hc
  rw [hc]
  have hi : Integrable (fun y : Fin (L₀ + 1) → ℝ => G κ (-∑ i, y i)) (sumLaw μ L₀) := by
    simpa using integrable_G_sum μ κ L₀ 0
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => G_nonneg _ _)]

lemma mean_nonneg (μ : DemandLaw) : 0 ≤ μ.mean :=
  integral_nonneg_of_ae (ae_nonneg μ)

lemma E_coord (μ : DemandLaw) (κ : Costs) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (κ.c * ω.1 k) ∂sampleLaw μ = ENNReal.ofReal (κ.c * μ.mean) := by
  have hmp := (mp_eval μ k).comp (mp_fst μ)
  have hc := hmp.lintegral_comp (f := fun d : ℝ => ENNReal.ofReal (κ.c * d))
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id))
  simp only [Function.comp] at hc
  have hi : Integrable (fun d : ℝ => κ.c * d) μ.law := μ.integrable.const_mul κ.c
  rw [hc, ← ofReal_integral_eq_lintegral_ofReal hi
    (by filter_upwards [ae_nonneg μ] with d hd; exact mul_nonneg κ.c_pos.le hd)]
  rw [integral_const_mul]
  rfl

lemma real_bound (i : ℕ) : (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (3 / 4) ^ i := by
  have h1 : ((i : ℝ) + 1) ≤ 2 * (3 / 2) ^ i := by
    induction i with
    | zero => norm_num
    | succ n ih =>
      have := one_le_pow₀ (show (1 : ℝ) ≤ 3 / 2 by norm_num) (n := n)
      push_cast; rw [pow_succ]; nlinarith
  calc (1 / 2 : ℝ) ^ (i + 1) * ((i : ℝ) + 1) ≤ (1 / 2) ^ (i + 1) * (2 * (3 / 2) ^ i) := by
        gcongr
    _ = (3 / 4) ^ i := by
        rw [pow_succ, show (3 / 4 : ℝ) = (1 / 2) * (3 / 2) by norm_num, mul_pow]; ring

lemma ghat_mean_ne_top : ∫⁻ k, (k : ℝ≥0∞) ∂ghatLaw ≠ ⊤ := by
  unfold ghatLaw
  rw [lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  refine ne_top_of_le_ne_top (ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_geometric (r := 3 / 4) (by norm_num))) (ENNReal.tsum_le_tsum fun i => ?_)
  rw [ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  push_cast
  exact real_bound i

lemma E0_fin (μ : DemandLaw) (κ : Costs) :
    ∫⁻ ω, ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range ω.2.2, ω.2.1 i) ∂sampleLaw μ ≠ ⊤ := by
  have hq : Measurable (fun q : Path × ℕ => ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range q.2, q.1 i)) := by
    refine measurable_from_prod_countable_left fun k => ?_
    simp only
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))
  have hc := (mp_snd μ).lintegral_comp hq
  rw [hc, lintegral_prod_symm _ hq.aemeasurable]
  set B := ∫⁻ d, ENNReal.ofReal (κ.c * |d|) ∂μ.law with hBdef
  have hB : B ≠ ⊤ := (Integrable.lintegral_lt_top (μ.integrable.abs.const_mul κ.c)).ne
  have inner : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (κ.c * ∑ i ∈ Finset.range k, x i) ∂pathLaw μ ≤
      (k : ℝ≥0∞) * B := by
    intro k
    have hmi : ∀ i, Measurable (fun x : Path => ENNReal.ofReal (κ.c * |x i|)) := fun i =>
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (continuous_abs.measurable.comp (measurable_pi_apply i)))
    calc _ ≤ ∫⁻ x, ∑ i ∈ Finset.range k, ENNReal.ofReal (κ.c * |x i|) ∂pathLaw μ :=
          lintegral_mono fun x => by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := κ.c_pos; positivity)]
            apply ENNReal.ofReal_le_ofReal
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_abs_self _) κ.c_pos.le
      _ = ∑ i ∈ Finset.range k, ∫⁻ x, ENNReal.ofReal (κ.c * |x i|) ∂pathLaw μ :=
          lintegral_finset_sum _ (fun i _ => hmi i)
      _ = ∑ _i ∈ Finset.range k, B := Finset.sum_congr rfl fun i _ =>
          (mp_eval μ i).lintegral_comp (f := fun d : ℝ => ENNReal.ofReal (κ.c * |d|))
            (ENNReal.measurable_ofReal.comp (measurable_const.mul continuous_abs.measurable))
      _ = (k : ℝ≥0∞) * B := by simp
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ghat_mean_ne_top hB)
    (le_trans (lintegral_mono inner) (le_of_eq (lintegral_mul_const B (Measurable.of_discrete))))

lemma tendsto_frac2 (A a : ℝ≥0∞) (hA : A ≠ ⊤) (ha : a ≠ ⊤) (L₀ : ℕ) :
    Tendsto (fun T : ℕ => (A + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * a) / T) atTop (𝓝 a) := by
  have e : ∀ᶠ T : ℕ in atTop,
      ENNReal.ofReal (a.toReal + (A.toReal - ((L₀ : ℝ) + 1) * a.toReal) / T) =
        (A + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * a) / T := by
    filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
    rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hA,
      ← ENNReal.ofReal_natCast (T - L₀ - 1), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ← ENNReal.ofReal_natCast T,
      ← ENNReal.ofReal_div_of_pos hT0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
      ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring
  refine Tendsto.congr' e ?_
  have : Tendsto (fun T : ℕ => a.toReal + (A.toReal - ((L₀ : ℝ) + 1) * a.toReal) / T) atTop
      (𝓝 (a.toReal + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [add_zero] at this
  have h2 := ENNReal.tendsto_ofReal this
  rwa [ENNReal.ofReal_toReal ha] at h2

lemma U_nonneg (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : 0 ≤ UConst μ κ L₀ :=
  add_nonneg (mul_nonneg κ.c_pos.le (mean_nonneg μ))
    (integral_nonneg fun _ => G_nonneg _ _)

lemma tbs00 (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) :
    tbsCost μ κ L₀ L 0 0 = ENNReal.ofReal (UConst μ κ L₀) := by
  set π₀ := tbsPolicy L₀ L 0 0
  set E : ℕ → ℝ≥0∞ := fun t => ∫⁻ ω, periodCost κ π₀ ω t ∂sampleLaw μ with hEdef
  have hae := ae_good μ
  have hEt : ∀ m, E (m + L₀ + 1) =
      ∫⁻ ω, ENNReal.ofReal (κ.c * v ω m) ∂sampleLaw μ +
        ENNReal.ofReal (∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀) := by
    intro m
    simp only [hEdef]
    rw [lintegral_congr_ae (by
      filter_upwards [hae] with ω hω
      exact cost_formula κ L₀ L ω hω.1 (Finset.sum_nonneg fun i _ => hω.2 i) m)]
    have hmeas : Measurable (fun ω : Sample =>
        ENNReal.ofReal (G κ (-∑ j : Fin (L₀ + 1), ω.1 (m + j)))) :=
      ENNReal.measurable_ofReal.comp ((continuous_G κ).measurable.comp
        (by fun_prop : Measurable fun ω : Sample => -∑ j : Fin (L₀ + 1), ω.1 (m + j)))
    rw [lintegral_add_right _ hmeas, E_win]
  have hE1 : ∀ m, 1 ≤ m → E (m + L₀ + 1) = ENNReal.ofReal (UConst μ κ L₀) := by
    intro m hm
    rw [hEt]
    have hv : ∀ ω, v ω m = ω.1 (m - 1) := fun ω => by simp only [v]; rw [if_neg (by omega)]
    simp only [hv]
    rw [E_coord, UConst, ENNReal.ofReal_add (mul_nonneg κ.c_pos.le (mean_nonneg μ))
      (integral_nonneg fun _ => G_nonneg _ _)]
  have hE0 : E (L₀ + 1) ≠ ⊤ := by
    have := hEt 0
    rw [zero_add] at this
    rw [this]
    refine ENNReal.add_ne_top.2 ⟨?_, ENNReal.ofReal_ne_top⟩
    simpa [v] using E0_fin μ κ
  have hsum : ∀ T, L₀ + 1 ≤ T → ∑ t ∈ Finset.Icc (L₀ + 1) T, E t =
      E (L₀ + 1) + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (UConst μ κ L₀) := by
    intro T hT
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hT, Finset.sum_insert (by simp)]
    congr 1
    have hc : ∀ t ∈ Finset.Icc (L₀ + 1 + 1) T, E t = ENNReal.ofReal (UConst μ κ L₀) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      have h := hE1 (t - L₀ - 1) (by omega)
      rwa [show t - L₀ - 1 + L₀ + 1 = t by omega] at h
    rw [Finset.sum_congr rfl hc]
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show T + 1 - (L₀ + 1 + 1) = T - L₀ - 1 by omega]
  show policyCost μ κ π₀ = _
  unfold policyCost
  rw [Filter.limsup_congr (f := atTop) (v := fun T : ℕ =>
    (E (L₀ + 1) + ((T - L₀ - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (UConst μ κ L₀)) / T) (by
      filter_upwards [eventually_ge_atTop (L₀ + 1)] with T hT
      rw [← hsum T hT])]
  exact (tendsto_frac2 _ _ hE0 ENNReal.ofReal_ne_top L₀).limsup_eq

end XGOB

namespace XGC4

/-- sign of a Bool -/
def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_sq (b : Bool) : sg b ^ 2 = 1 := by cases b <;> simp [sg]

lemma sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ s, F s = ∑ s : Fin n → Bool, (F (Fin.cons true s) + F (Fin.cons false s)) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  rfl

lemma S_cons {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Bool) (s : Fin n → Bool) :
    ∑ i, sg ((Fin.cons b s : Fin (n + 1) → Bool) i) * a i
      = sg b * a 0 + ∑ i, sg (s i) * a i.succ := by
  rw [Fin.sum_univ_succ]
  simp

lemma moments (n : ℕ) : ∀ (a : Fin n → ℝ) (x : ℝ),
    ∑ s : Fin n → Bool, (x + ∑ i, sg (s i) * a i) ^ 2 = 2 ^ n * (x ^ 2 + ∑ i, a i ^ 2) ∧
    ∑ s : Fin n → Bool, (x + ∑ i, sg (s i) * a i) ^ 4 =
      2 ^ n * (x ^ 4 + 6 * x ^ 2 * (∑ i, a i ^ 2) + 3 * (∑ i, a i ^ 2) ^ 2
        - 2 * ∑ i, a i ^ 4) := by
  induction n with
  | zero => intro a x; simp
  | succ n ih =>
    intro a x
    obtain ⟨h2p, h4p⟩ := ih (fun i => a i.succ) (x + a 0)
    obtain ⟨h2m, h4m⟩ := ih (fun i => a i.succ) (x - a 0)
    have hstep : ∀ k : ℕ, ∑ s : Fin (n + 1) → Bool, (x + ∑ i, sg (s i) * a i) ^ k =
        ∑ s : Fin n → Bool, ((x + a 0 + ∑ i, sg (s i) * a i.succ) ^ k
          + (x - a 0 + ∑ i, sg (s i) * a i.succ) ^ k) := by
      intro k
      rw [sum_cons]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sg, if_true, Bool.false_eq_true, if_false]
      ring
    have hA : ∑ i : Fin (n + 1), a i ^ 2 = a 0 ^ 2 + ∑ i : Fin n, a i.succ ^ 2 := Fin.sum_univ_succ _
    have hB : ∑ i : Fin (n + 1), a i ^ 4 = a 0 ^ 4 + ∑ i : Fin n, a i.succ ^ 4 := Fin.sum_univ_succ _
    rw [hstep, hstep, hA, hB, Finset.sum_add_distrib, Finset.sum_add_distrib, h2p, h2m, h4p, h4m]
    constructor <;> ring

/-- Khintchine (L¹ lower bound, constant 1/√3) in the form used below:
`2^n · ∑|a i| ≤ 2 √n · ∑_s |∑ σ_i a_i|`. -/
lemma khintchine (n : ℕ) (a : Fin n → ℝ) :
    2 ^ n * ∑ i, |a i| ≤ 2 * Real.sqrt n * ∑ s : Fin n → Bool, |∑ i, sg (s i) * a i| := by
  obtain ⟨h2, h4⟩ := moments n a 0
  simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul, add_zero, zero_add] at h2 h4
  set A := ∑ i, a i ^ 2 with hAdef
  set B := ∑ i, a i ^ 4
  set S : (Fin n → Bool) → ℝ := fun s => ∑ i, sg (s i) * a i with hS
  set M1 := ∑ s, |S s|
  set M2 := ∑ s, S s ^ 2
  set M3 := ∑ s, |S s| ^ 3
  set M4 := ∑ s, S s ^ 4
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => by positivity)
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => by positivity)
  have hM1 : 0 ≤ M1 := Finset.sum_nonneg (fun i _ => by positivity)
  have hM3 : 0 ≤ M3 := Finset.sum_nonneg (fun i _ => by positivity)
  have h2' : M2 = 2 ^ n * A := h2
  have h4' : M4 ≤ 2 ^ n * (3 * A ^ 2) := by
    rw [h4]; have : (0:ℝ) < 2 ^ n := by positivity
    nlinarith
  -- CS 1: M2² ≤ M1 M3
  have cs1 : M2 ^ 2 ≤ M1 * M3 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => Real.sqrt |S s|)
      (fun s => Real.sqrt |S s| * |S s|)
    have e1 : ∀ s, Real.sqrt |S s| * (Real.sqrt |S s| * |S s|) = S s ^ 2 := by
      intro s
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _), ← sq, sq_abs]
    have e2 : ∀ s, Real.sqrt |S s| ^ 2 = |S s| := fun s => Real.sq_sqrt (abs_nonneg _)
    have e3 : ∀ s, (Real.sqrt |S s| * |S s|) ^ 2 = |S s| ^ 3 := by
      intro s; rw [mul_pow, e2]; ring
    simp only [e1, e2, e3] at this
    exact this
  -- CS 2: M3² ≤ M2 M4
  have cs2 : M3 ^ 2 ≤ M2 * M4 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s => |S s|) (fun s => S s ^ 2)
    have e1 : ∀ s, |S s| * S s ^ 2 = |S s| ^ 3 := by
      intro s; rw [← sq_abs (S s)]; ring
    have e2 : ∀ s, |S s| ^ 2 = S s ^ 2 := fun s => sq_abs _
    have e3 : ∀ s, (S s ^ 2) ^ 2 = S s ^ 4 := fun s => by ring
    simp only [e1, e2, e3] at this
    exact this
  -- combine: 4^n A ≤ 3 M1²
  have hP : (0:ℝ) < 2 ^ n := by positivity
  have key : (2 ^ n) ^ 2 * A ≤ 3 * M1 ^ 2 := by
    rcases hA0.eq_or_lt with hA | hA
    · rw [← hA]; simp; positivity
    have hM2pos : 0 < M2 := by rw [h2']; positivity
    -- M2^4 ≤ M1^2 M3^2 ≤ M1^2 M2 M4
    have h1 : M2 ^ 4 ≤ M1 ^ 2 * (M2 * M4) := by
      calc M2 ^ 4 = (M2 ^ 2) ^ 2 := by ring
        _ ≤ (M1 * M3) ^ 2 := pow_le_pow_left₀ (by positivity) cs1 2
        _ = M1 ^ 2 * M3 ^ 2 := by ring
        _ ≤ M1 ^ 2 * (M2 * M4) := mul_le_mul_of_nonneg_left cs2 (by positivity)
    have h3 : M2 ^ 3 ≤ M1 ^ 2 * M4 := by
      have : M2 * M2 ^ 3 ≤ M2 * (M1 ^ 2 * M4) := by nlinarith
      exact le_of_mul_le_mul_left this hM2pos
    have h5 : M2 ^ 3 ≤ M1 ^ 2 * (2 ^ n * (3 * A ^ 2)) :=
      h3.trans (mul_le_mul_of_nonneg_left h4' (by positivity))
    rw [h2'] at h5
    have : (2 ^ n * A ^ 2) * ((2 ^ n) ^ 2 * A) ≤ (2 ^ n * A ^ 2) * (3 * M1 ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  -- (∑|a|)² ≤ n A
  have csA : (∑ i, |a i|) ^ 2 ≤ n * A := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => |a i|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs] at this
    exact this
  have hsq : (2 ^ n * ∑ i, |a i|) ^ 2 ≤ (2 * Real.sqrt n * M1) ^ 2 := by
    have hn : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    calc (2 ^ n * ∑ i, |a i|) ^ 2 = (2 ^ n) ^ 2 * (∑ i, |a i|) ^ 2 := by ring
      _ ≤ (2 ^ n) ^ 2 * (n * A) := mul_le_mul_of_nonneg_left csA (by positivity)
      _ = n * ((2 ^ n) ^ 2 * A) := by ring
      _ ≤ n * (3 * M1 ^ 2) := mul_le_mul_of_nonneg_left key (Nat.cast_nonneg n)
      _ ≤ 4 * n * M1 ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg M1]
      _ = (2 * Real.sqrt n * M1) ^ 2 := by rw [mul_pow, mul_pow, hn]; ring
  have h0 : 0 ≤ 2 * Real.sqrt n * M1 := by positivity
  exact (pow_le_pow_iff_left₀ (by positivity) h0 (by norm_num)).1 hsq

end XGC4

namespace XGC4

open MeasureTheory ProbabilityTheory XinGoldbergTBS.Asymptotic
open scoped ENNReal

lemma eta0_le (μ : DemandLaw) (x : ℝ) : eta0 μ ≤ ∫ y, |x - y| ∂μ.law :=
  ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact integral_nonneg (fun _ => abs_nonneg _)⟩ x

lemma pair_ge (μ : DemandLaw) :
    ENNReal.ofReal (eta0 μ) ≤ ∫⁻ q : ℝ × ℝ, ENNReal.ofReal |q.1 - q.2| ∂(μ.law.prod μ.law) := by
  rw [lintegral_prod _ (by fun_prop)]
  calc ENNReal.ofReal (eta0 μ) = ∫⁻ x : ℝ, ENNReal.ofReal (eta0 μ) ∂μ.law := by simp
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      dsimp only
      have hint : Integrable (fun y : ℝ => |x - y|) μ.law :=
        ((integrable_const x).sub μ.integrable).abs
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (eta0_le μ x)

/-- coordinatewise swap pattern -/
def swp {n : ℕ} (s : Fin n → Bool) (i : Fin n) : ℝ × ℝ → ℝ × ℝ := if s i then id else Prod.swap

lemma mp_swp (μ : DemandLaw) {n : ℕ} (s : Fin n → Bool) :
    MeasurePreserving (fun p : Fin n → ℝ × ℝ => fun i => swp s i (p i))
      (Measure.pi fun _ => μ.law.prod μ.law) (Measure.pi fun _ => μ.law.prod μ.law) := by
  apply measurePreserving_pi
  intro i
  unfold swp
  split_ifs
  · exact MeasurePreserving.id _
  · exact Measure.measurePreserving_swap

lemma swp_diff {n : ℕ} (s : Fin n → Bool) (i : Fin n) (q : ℝ × ℝ) :
    (swp s i q).1 - (swp s i q).2 = sg (s i) * (q.1 - q.2) := by
  cases h : s i <;> simp [swp, sg, h]

lemma sym_ge (μ : DemandLaw) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (Real.sqrt n * eta0 μ / 2) ≤
      ∫⁻ p : Fin n → ℝ × ℝ, ENNReal.ofReal |∑ i, ((p i).1 - (p i).2)|
        ∂(Measure.pi fun _ => μ.law.prod μ.law) := by
  set ν := Measure.pi fun _ : Fin n => μ.law.prod μ.law
  set F : (Fin n → ℝ × ℝ) → ℝ≥0∞ := fun p => ENNReal.ofReal |∑ i, ((p i).1 - (p i).2)| with hF
  have hFm : Measurable F := by
    rw [hF]; fun_prop
  clear_value F
  have hsw : ∀ s : Fin n → Bool, ∫⁻ p, F (fun i => swp s i (p i)) ∂ν = ∫⁻ p, F p ∂ν :=
    fun s => (mp_swp μ s).lintegral_comp hFm
  have hsum : (2 ^ n : ℝ≥0∞) * ∫⁻ p, F p ∂ν =
      ∫⁻ p, ∑ s : Fin n → Bool, F (fun i => swp s i (p i)) ∂ν := by
    rw [lintegral_finsetSum (f := fun (s : Fin n → Bool) (p : Fin n → ℝ × ℝ) => F (fun i => swp s i (p i)))
      Finset.univ
      (fun s _ => hFm.comp (mp_swp μ s).measurable)]
    simp only [hsw, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hsn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  set c : ℝ := 2 ^ n / (2 * Real.sqrt n) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ p : Fin n → ℝ × ℝ, ENNReal.ofReal (c * ∑ i, |(p i).1 - (p i).2|) ≤
      ∑ s : Fin n → Bool, F (fun i => swp s i (p i)) := by
    intro p
    simp only [hF, swp_diff]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have := khintchine n (fun i => (p i).1 - (p i).2)
    rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [this]
  have hint : ∫⁻ p, ENNReal.ofReal (c * ∑ i, |(p i).1 - (p i).2|) ∂ν =
      ENNReal.ofReal c * ∑ i : Fin n, ∫⁻ q : ℝ × ℝ, ENNReal.ofReal |q.1 - q.2| ∂(μ.law.prod μ.law) := by
    simp_rw [ENNReal.ofReal_mul hc0]
    rw [lintegral_const_mul _ (by fun_prop)]
    congr 1
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    rw [lintegral_finsetSum _ (fun i _ => by fun_prop)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (measurePreserving_eval (fun _ => μ.law.prod μ.law) i).lintegral_comp
      (f := fun q : ℝ × ℝ => ENNReal.ofReal |q.1 - q.2|) (by fun_prop)
  have hlow := pair_ge μ
  have hη : 0 ≤ eta0 μ := le_ciInf (fun z => integral_nonneg (fun _ => abs_nonneg _))
  have hreal : c * (n * eta0 μ) = 2 ^ n * (Real.sqrt n * eta0 μ / 2) := by
    have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
    calc c * (n * eta0 μ) = c * ((Real.sqrt n * Real.sqrt n) * eta0 μ) := by rw [hs]
      _ = 2 ^ n * (Real.sqrt n * eta0 μ / 2) := by rw [hc]; field_simp
  have key : (2 ^ n : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt n * eta0 μ / 2) ≤
      (2 ^ n : ℝ≥0∞) * ∫⁻ p, F p ∂ν := by
    rw [hsum]
    calc (2 ^ n : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt n * eta0 μ / 2)
        = ENNReal.ofReal c * ∑ i : Fin n, ENNReal.ofReal (eta0 μ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul hc0, hreal, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal c * ∑ i : Fin n,
            ∫⁻ q : ℝ × ℝ, ENNReal.ofReal |q.1 - q.2| ∂(μ.law.prod μ.law) := by
          gcongr
      _ = ∫⁻ p, ENNReal.ofReal (c * ∑ i, |(p i).1 - (p i).2|) ∂ν := hint.symm
      _ ≤ _ := lintegral_mono hpt
  have hfin := (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1 key
  exact hfin

lemma half_ge (μ : DemandLaw) (n : ℕ) (hn : 0 < n) (a : ℝ) :
    ENNReal.ofReal (Real.sqrt n * eta0 μ / 4) ≤
      ∫⁻ x : Fin n → ℝ, ENNReal.ofReal |a - ∑ i, x i| ∂(Measure.pi fun _ => μ.law) := by
  set π := Measure.pi fun _ : Fin n => μ.law
  have e := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => μ.law) (fun _ => μ.law)
  have h1 := sym_ge μ n hn
  have h2 : ∫⁻ p : Fin n → ℝ × ℝ, ENNReal.ofReal |∑ i, ((p i).1 - (p i).2)|
        ∂(Measure.pi fun _ => μ.law.prod μ.law)
      = ∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal |∑ i, z.1 i - ∑ i, z.2 i| ∂(π.prod π) := by
    rw [← e.lintegral_comp (by fun_prop)]
    congr 1; ext p
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      Finset.sum_sub_distrib]
  have h3 : ∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal |∑ i, z.1 i - ∑ i, z.2 i| ∂(π.prod π)
      ≤ 2 * ∫⁻ x, ENNReal.ofReal |a - ∑ i, x i| ∂π := by
    calc _ ≤ ∫⁻ z : (Fin n → ℝ) × (Fin n → ℝ),
          (ENNReal.ofReal |a - ∑ i, z.1 i| + ENNReal.ofReal |a - ∑ i, z.2 i|) ∂(π.prod π) := by
          apply lintegral_mono; intro z
          dsimp only
          rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          calc |∑ i, z.1 i - ∑ i, z.2 i| ≤ |∑ i, z.1 i - a| + |a - ∑ i, z.2 i| := abs_sub_le _ _ _
            _ = |a - ∑ i, z.1 i| + |a - ∑ i, z.2 i| := by rw [abs_sub_comm (∑ i, z.1 i) a]
      _ = ∫⁻ x, ENNReal.ofReal |a - ∑ i, x i| ∂π + ∫⁻ x, ENNReal.ofReal |a - ∑ i, x i| ∂π := by
          rw [lintegral_add_left (by fun_prop)]
          congr 1
          · rw [lintegral_prod _ (by fun_prop)]; simp
          · rw [lintegral_prod _ (by fun_prop)]; simp
      _ = 2 * _ := by rw [two_mul]
  have h4 : ENNReal.ofReal (Real.sqrt n * eta0 μ / 2) = 2 * ENNReal.ofReal (Real.sqrt n * eta0 μ / 4) := by
    rw [show Real.sqrt n * eta0 μ / 2 = 2 * (Real.sqrt n * eta0 μ / 4) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have h5 : 2 * ENNReal.ofReal (Real.sqrt n * eta0 μ / 4) ≤ 2 * ∫⁻ x, ENNReal.ofReal |a - ∑ i, x i| ∂π := by
    rw [← h4]; exact h1.trans (h2 ▸ h3)
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h5

lemma omega_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : DemandLaw) {n : ℕ} (hn : 0 < n)
    (A : Ω → ℝ) (V : Ω → Fin n → ℝ) (hA : Measurable A) (hV : Measurable V)
    (hind : IndepFun A V P) (hlaw : P.map V = Measure.pi fun _ => μ.law) :
    ENNReal.ofReal (Real.sqrt n * eta0 μ / 4) ≤ ∫⁻ ω, ENNReal.ofReal |A ω - ∑ i, V ω i| ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hV.aemeasurable).1 hind
  rw [hlaw] at hmap
  have hAV : Measurable (fun ω => (A ω, V ω)) := hA.prodMk hV
  have : ∫⁻ ω, ENNReal.ofReal |A ω - ∑ i, V ω i| ∂P =
      ∫⁻ z : ℝ × (Fin n → ℝ), ENNReal.ofReal |z.1 - ∑ i, z.2 i| ∂(P.map (fun ω => (A ω, V ω))) := by
    rw [lintegral_map (by fun_prop) hAV]
  rw [this, hmap, lintegral_prod _ (by fun_prop)]
  have : IsProbabilityMeasure (P.map A) := Measure.isProbabilityMeasure_map hA.aemeasurable
  calc ENNReal.ofReal (Real.sqrt n * eta0 μ / 4)
      = ∫⁻ a, ENNReal.ofReal (Real.sqrt n * eta0 μ / 4) ∂(P.map A) := by simp
    _ ≤ _ := lintegral_mono (fun a => half_ge μ n hn a)

end XGC4

namespace XGC4

open MeasureTheory ProbabilityTheory XinGoldbergTBS.Asymptotic
open scoped ENNReal

/-- choose `m` -/
lemma pick (e b' V : ℝ) (N : ℕ) (he : 0 < e) (hb : 0 < b') (hV : 0 ≤ V)
    (hN : (e ^ 2)⁻¹ + 1 < N)
    (hcond : V + e < (b' / (2 * e)) * min 1 (b' / 2))
    (hall : ∀ m : ℕ, 1 ≤ m → m ≤ N → b' * Real.sqrt m ≤ V + m * e) : False := by
  set t : ℝ := min (1 / e) (b' / (2 * e)) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have hte : t * e ≤ b' / 2 := by
    have : t ≤ b' / (2 * e) := min_le_right _ _
    calc t * e ≤ b' / (2 * e) * e := mul_le_mul_of_nonneg_right this he.le
      _ = b' / 2 := by field_simp
  have ht1 : t ≤ 1 / e := min_le_left _ _
  have ht2 : t ^ 2 ≤ (e ^ 2)⁻¹ := by
    have : t ^ 2 ≤ (1 / e) ^ 2 := pow_le_pow_left₀ ht0.le ht1 2
    simpa [one_div, inv_pow] using this
  set m : ℕ := ⌈t ^ 2⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    rw [hm]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hmlt : (m : ℝ) < t ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmN : m ≤ N := by
    have : (m : ℝ) < N := by linarith
    exact_mod_cast this.le
  have hmge : t ^ 2 ≤ m := Nat.le_ceil _
  have hsq : t ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hmge
  have h := hall m hm1 hmN
  have h1 : b' * t ≤ b' * Real.sqrt m := mul_le_mul_of_nonneg_left hsq hb.le
  have h2 : (m : ℝ) * e ≤ (t ^ 2 + 1) * e := mul_le_mul_of_nonneg_right hmlt.le he.le
  have h3 : t ^ 2 * e ≤ b' / 2 * t := by nlinarith
  have hkey : b' * t / 2 ≤ V + e := by nlinarith
  have heq : b' * t / 2 = (b' / (2 * e)) * min 1 (b' / 2) := by
    rw [ht]
    rcases le_total 1 (b' / 2) with h12 | h12
    · rw [min_eq_left h12, min_eq_left (by
        rw [div_le_div_iff₀ he (by positivity)]; nlinarith)]
      field_simp
    · rw [min_eq_right h12, min_eq_right (by
        rw [div_le_div_iff₀ (by positivity) he]; nlinarith)]
      field_simp
  linarith

/-- the numerical condition -/
lemma cond_num (e b' U mn E X p : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 3200) (hb : 0 < b')
    (hmn : 0 < mn) (hp : 0 < p) (hp8 : p ^ 2 ≤ 1 / 8) (hU : 0 < U)
    (h1 : e ≤ 4 * b' ^ 2 * p ^ 2)
    (h2 : e * (2250000 * X ^ 2) ≤ mn ^ 2 * p ^ 2 * b' ^ 2)
    (hXU : U + 1 ≤ X) (hX0 : 64 * mn * E ≤ X) (hEη : 4 * b' ≤ E) :
    U / mn + e < (b' / (2 * e)) * min 1 (b' / 2) := by
  have hX : 0 < X := by linarith
  rcases le_total (b' / 2) 1 with hb2 | hb2
  · rw [min_eq_right hb2]
    -- need U/mn + e < b'^2/(4e)
    have hA : 4 * e ^ 2 < b' ^ 2 / 2 := by nlinarith
    have hB : 8 * e * U ≤ mn * b' ^ 2 := by
      rcases le_total (32 * p ^ 2 * U) mn with hc | hc
      · have : 8 * e * U ≤ 8 * (4 * b' ^ 2 * p ^ 2) * U := by
          have := mul_le_mul_of_nonneg_right h1 hU.le; nlinarith
        nlinarith
      · -- 8 U mn p² ≤ 2250000 X²
        have hp4 : p ^ 2 * p ^ 2 ≤ 1 / 64 := by nlinarith
        have hq : 8 * U * mn * p ^ 2 ≤ 2250000 * X ^ 2 := by
          have : 8 * U * mn * p ^ 2 ≤ 8 * U * (32 * p ^ 2 * U) * p ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity)
          have hUX : U ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hU.le (by linarith) 2
          nlinarith
        -- e * 2250000 X² ≤ mn² p² b'²  ⇒  8 e U ≤ mn b'²
        have h2' : 8 * e * U * (2250000 * X ^ 2) ≤ 8 * U * (mn ^ 2 * p ^ 2 * b' ^ 2) := by
          nlinarith
        have h3 : 8 * U * (mn ^ 2 * p ^ 2 * b' ^ 2) ≤ mn * b' ^ 2 * (2250000 * X ^ 2) := by
          have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ mn * b' ^ 2)
          nlinarith
        have hpos : 0 < 2250000 * X ^ 2 := by positivity
        exact le_of_mul_le_mul_right (h2'.trans h3) hpos
    have hgoal : U / mn + e < b' / (2 * e) * (b' / 2) := by
      have : b' / (2 * e) * (b' / 2) = b' ^ 2 / (4 * e) := by field_simp; ring
      rw [this, div_add' _ _ _ hmn.ne', div_lt_div_iff₀ hmn (by positivity)]
      nlinarith
    exact hgoal
  · rw [min_eq_left hb2]
    have hX2 : 256 * mn * b' * U ≤ X ^ 2 := by
      have h4 : 64 * mn * (4 * b') ≤ X := le_trans (by nlinarith) hX0
      nlinarith
    have hB : 4 * e * U < mn * b' := by
      have h2' : 4 * e * U * (2250000 * X ^ 2) ≤ 4 * U * (mn ^ 2 * p ^ 2 * b' ^ 2) := by
        nlinarith
      have h3 : 4 * U * (mn ^ 2 * p ^ 2 * b' ^ 2) < mn * b' * (2250000 * X ^ 2) := by
        have hpos2 : 0 < mn ^ 2 * b' ^ 2 * U := by positivity
        have h7 := mul_le_mul_of_nonneg_left hp8 (by positivity : (0:ℝ) ≤ 4 * U * mn ^ 2 * b' ^ 2)
        have h5 := mul_le_mul_of_nonneg_left hX2 (by positivity : (0:ℝ) ≤ mn * b')
        nlinarith
      have hpos : 0 < 2250000 * X ^ 2 := by positivity
      exact lt_of_mul_lt_mul_right (lt_of_le_of_lt h2' h3) hpos.le
    have hgoal : U / mn + e < b' / (2 * e) * 1 := by
      rw [mul_one, div_add' _ _ _ hmn.ne', div_lt_div_iff₀ hmn (by positivity)]
      have he2 : e * e ≤ 1 / 3200 * (1 / 3200) := mul_le_mul he1 he1 he.le (by norm_num)
      have h6 : 2 * (e * e) * mn < mn * b' / 2 := by
        nlinarith [mul_le_mul_of_nonneg_right he2 hmn.le]
      nlinarith
    exact hgoal

end XGC4

namespace XGC4

open MeasureTheory ProbabilityTheory XinGoldbergTBS.Asymptotic
open scoped ENNReal

/-- `chiN` with the vector as argument -/
def cN (L₀ L : ℕ) (c : Fin (L - L₀ - 1) → ℝ) (j : ℕ) : ℝ :=
  if h : j < L - L₀ - 1 then c ⟨j, h⟩ else 0

lemma measurable_cN (L₀ L j : ℕ) : Measurable (fun c : Fin (L - L₀ - 1) → ℝ => cN L₀ L c j) := by
  unfold cN
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma measurable_chiN {Ω : Type*} [MeasurableSpace Ω] (L₀ L : ℕ) (χ : Ω → Fin (L - L₀ - 1) → ℝ)
    (hχ : Measurable χ) (j : ℕ) : Measurable (fun ω => chiN L₀ L χ ω j) :=
  (measurable_cN L₀ L j).comp hχ

lemma measurable_qN {Ω : Type*} [MeasurableSpace Ω] (L₀ L : ℕ) (q : Ω → Fin (L - L₀) → ℝ)
    (hq : Measurable q) (j : ℕ) : Measurable (fun ω => qN L₀ L q ω j) := by
  unfold qN
  split_ifs
  · exact (measurable_pi_apply _).comp hq
  · exact measurable_const

lemma UConst_pos (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : 0 < UConst μ κ L₀ := by
  unfold UConst
  have h1 : 0 < κ.c * μ.mean := mul_pos κ.c_pos (XGT1.mean_pos μ)
  have h2 : 0 ≤ ∫ y, G κ (-∑ i, y i) ∂sumLaw μ L₀ := integral_nonneg (fun y => XGT1.G_nonneg κ _)
  linarith

/-- The key inequality for one index `k` of a witness. -/
theorem wit_bound (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D) (k : Fin (L - L₀)) :
    Real.sqrt ((k.val + (L₀ + 1) : ℕ) : ℝ) * eta0 μ / 4 ≤
      UConst μ κ L₀ / min κ.b κ.h + (k.val + 1) * (μ.mean - rL P L₀ L χ) := by
  haveI := hw.isProb
  have hL0 : 0 < L - L₀ := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  set z0 : Fin (L - L₀) := ⟨0, hL0⟩
  set n : ℕ := k.val + (L₀ + 1) with hn
  have hn0 : 0 < n := by omega
  set εq : ℝ := ∫ ω, q ω z0 ∂P with hεq
  have hqN0 : ∀ ω, qN L₀ L q ω 0 = q ω z0 := fun ω => by simp [qN, hL0, z0]
  have hε : μ.mean - rL P L₀ L χ = εq := by
    have := hw.mean_eq
    simp only [hqN0] at this
    unfold rL; linarith
  rw [hε]
  -- measurability
  have hmq : ∀ j, Measurable (fun ω => q ω j) := fun j => (measurable_pi_apply j).comp hw.measurable_q
  have hmD := hw.measurable_D
  -- the pieces
  set A : Ω → ℝ := fun ω => I ω + ∑ i ∈ Finset.range k.val, chiN L₀ L χ ω i with hA
  set V : Ω → Fin n → ℝ := fun ω i => D i ω with hV
  set Y : Ω → ℝ := fun ω => I ω + ∑ i ∈ Finset.range k.val, (qN L₀ L q ω i + chiN L₀ L χ ω i - D i ω)
      + q ω k - ∑ i ∈ Finset.range (L₀ + 1), D (k.val + i) ω with hY
  set Y0 : Ω → ℝ := fun ω => I ω + qN L₀ L q ω 0 - ∑ i ∈ Finset.range (L₀ + 1), D i ω with hY0
  have hAm : Measurable A := hw.measurable_I.add
    (Finset.measurable_sum _ (fun i _ => measurable_chiN L₀ L χ hw.measurable_chi i))
  have hVm : Measurable V := measurable_pi_lambda _ (fun i => hmD i)
  have hYm : Measurable Y := by
    refine ((hw.measurable_I.add (Finset.measurable_sum _ (fun i _ => ?_))).add (hmq k)).sub
      (Finset.measurable_sum _ (fun i _ => hmD _))
    exact ((measurable_qN L₀ L q hw.measurable_q i).add
      (measurable_chiN L₀ L χ hw.measurable_chi i)).sub (hmD i)
  -- independence
  have hind : IndepFun A V P := by
    have h := hw.indep_chi_I.comp
      (φ := fun p : (Fin (L - L₀ - 1) → ℝ) × ℝ => p.2 + ∑ i ∈ Finset.range k.val, cN L₀ L p.1 i)
      (ψ := fun y : ℕ → ℝ => fun i : Fin n => y i)
      (measurable_snd.add (Finset.measurable_sum _ (fun i _ => (measurable_cN L₀ L i).comp measurable_fst)))
      (measurable_pi_lambda _ (fun i => measurable_pi_apply _))
    exact h
  have hlaw : P.map V = Measure.pi fun _ => μ.law := by
    have h1 : iIndepFun (fun i : Fin n => D i) P := hw.indep_D.precomp Fin.val_injective
    rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun i : Fin n => D i)
      (fun i => (hmD i).aemeasurable)).1 h1]
    simp [hw.law_D]
  have hlow := omega_ge P μ hn0 A V hAm hVm hind hlaw
  -- pointwise decomposition
  have hpt : ∀ ω, |A ω - ∑ i, V ω i| ≤
      |Y ω| + (∑ i ∈ Finset.range k.val, |qN L₀ L q ω i| + |q ω k|) := by
    intro ω
    have hT : ∑ i, V ω i = ∑ i ∈ Finset.range k.val, D i ω
        + ∑ i ∈ Finset.range (L₀ + 1), D (k.val + i) ω := by
      rw [hV]; dsimp only
      rw [Fin.sum_univ_eq_sum_range (fun i => D i ω) n, hn, Finset.sum_range_add]
    have hdec : A ω - ∑ i, V ω i = Y ω - (∑ i ∈ Finset.range k.val, qN L₀ L q ω i + q ω k) := by
      rw [hT, hA, hY]; dsimp only
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
    rw [hdec]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    exact (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
  -- each q term
  have hq_each : ∀ j : Fin (L - L₀), ∫⁻ ω, ENNReal.ofReal |q ω j| ∂P = ENNReal.ofReal εq := by
    intro j
    have h1 : ∫⁻ ω, ENNReal.ofReal |q ω j| ∂P = ∫⁻ ω, ENNReal.ofReal |q ω z0| ∂P :=
      ((hw.ident_q j z0).comp (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal |x|)).lintegral_eq
    rw [h1, hεq, ofReal_integral_eq_lintegral_ofReal (hw.integrable_q z0)]
    · apply lintegral_congr_ae
      filter_upwards [hw.nonneg] with ω hω
      rw [abs_of_nonneg (hω.2 z0)]
    · filter_upwards [hw.nonneg] with ω hω
      exact hω.2 z0
  have hqN_each : ∀ i ∈ Finset.range k.val,
      ∫⁻ ω, ENNReal.ofReal |qN L₀ L q ω i| ∂P = ENNReal.ofReal εq := by
    intro i hi
    have hi' : i < L - L₀ := lt_trans (Finset.mem_range.1 hi) k.isLt
    have : ∀ ω, qN L₀ L q ω i = q ω ⟨i, hi'⟩ := fun ω => by simp [qN, hi']
    simp only [this]
    exact hq_each _
  have hεq0 : 0 ≤ εq := by
    rw [hεq]; apply integral_nonneg_of_ae
    filter_upwards [hw.nonneg] with ω hω
    exact hω.2 z0
  -- integrate the decomposition
  have hint : ∫⁻ ω, ENNReal.ofReal |A ω - ∑ i, V ω i| ∂P ≤
      ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P + ENNReal.ofReal ((k.val + 1) * εq) := by
    calc ∫⁻ ω, ENNReal.ofReal |A ω - ∑ i, V ω i| ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal |Y ω| + (∑ i ∈ Finset.range k.val, ENNReal.ofReal |qN L₀ L q ω i|
            + ENNReal.ofReal |q ω k|)) ∂P := by
          apply lintegral_mono; intro ω
          dsimp only
          rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
            ← ENNReal.ofReal_add (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (abs_nonneg _),
            ← ENNReal.ofReal_add (abs_nonneg _) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt ω)
      _ = ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P + (∑ i ∈ Finset.range k.val,
            ∫⁻ ω, ENNReal.ofReal |qN L₀ L q ω i| ∂P + ∫⁻ ω, ENNReal.ofReal |q ω k| ∂P) := by
          rw [lintegral_add_left (by fun_prop), lintegral_add_right _ (by fun_prop),
            lintegral_finsetSum _ (fun i _ => by
              have := measurable_qN L₀ L q hw.measurable_q i
              fun_prop)]
      _ = ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P + ENNReal.ofReal ((k.val + 1) * εq) := by
          rw [Finset.sum_congr rfl hqN_each, hq_each k, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          congr 1
          rw [show ((k.val : ℝ) + 1) * εq = k.val * εq + εq by ring,
            ENNReal.ofReal_add (by positivity) hεq0, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
  -- the G bound
  have hG_meas : Measurable fun x : ℝ => ENNReal.ofReal (G κ x) :=
    ENNReal.measurable_ofReal.comp (XGT1.continuous_G κ).measurable
  have hGY : ∫⁻ ω, ENNReal.ofReal (G κ (Y ω)) ∂P = ∫⁻ ω, ENNReal.ofReal (G κ (Y0 ω)) ∂P :=
    ((hw.stationary k).comp hG_meas).lintegral_eq
  have hOPT : OPT μ κ L₀ L ≤ ENNReal.ofReal (UConst μ κ L₀) := by
    rw [← XGOB.tbs00 μ κ L₀ L]
    exact iInf_le _ (tbsPolicy L₀ L 0 0)
  have hY0U : ∫⁻ ω, ENNReal.ofReal (G κ (Y0 ω)) ∂P ≤ ENNReal.ofReal (UConst μ κ L₀) :=
    le_trans le_add_self (hw.opt_ge.trans hOPT)
  have hmn : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hYU : ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P ≤ ENNReal.ofReal (UConst μ κ L₀ / min κ.b κ.h) := by
    have h1 : ENNReal.ofReal (min κ.b κ.h) * ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P ≤
        ENNReal.ofReal (UConst μ κ L₀) := by
      rw [← lintegral_const_mul _ (by fun_prop)]
      refine le_trans ?_ (hGY ▸ hY0U)
      apply lintegral_mono; intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul hmn.le]
      exact ENNReal.ofReal_le_ofReal (XGT1.G_ge κ (Y ω))
    have h2 : ENNReal.ofReal (UConst μ κ L₀) =
        ENNReal.ofReal (min κ.b κ.h) * ENNReal.ofReal (UConst μ κ L₀ / min κ.b κ.h) := by
      rw [← ENNReal.ofReal_mul hmn.le, mul_div_cancel₀ _ hmn.ne']
    rw [h2] at h1
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hmn) ENNReal.ofReal_ne_top).1 h1
  have hfin := hlow.trans (hint.trans (add_le_add hYU le_rfl))
  rw [← ENNReal.ofReal_add (div_nonneg ((UConst_pos μ κ L₀).le) hmn.le) (by positivity)] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (by
    have := (UConst_pos μ κ L₀).le
    positivity)).1 hfin

end XGC4

namespace XGC4

open MeasureTheory ProbabilityTheory XinGoldbergTBS.Asymptotic
open scoped ENNReal

lemma eta0_le_mean (μ : DemandLaw) : eta0 μ ≤ μ.mean := by
  refine (eta0_le μ 0).trans (le_of_eq ?_)
  unfold DemandLaw.mean
  apply integral_congr_ae
  filter_upwards [XGT1.ae_nonneg μ] with y hy
  simp [abs_of_nonneg hy]

end XGC4

open MeasureTheory ProbabilityTheory Filter XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (hL : (eps0 μ κ L₀ ^ 2)⁻¹ + L₀ + 1 < (L : ℝ)) :
    rL P L₀ L χ < μ.mean - eps0 μ κ L₀ := by
  by_contra hcon
  rw [not_lt] at hcon
  have he := XGT1.eps0_pos μ κ L₀
  have he1 := XGT1.eps0_le_small μ κ L₀
  obtain ⟨hp, hp8⟩ := XGT1.p0hat_facts μ
  have hη := XGT1.eta0_pos μ
  have hmn : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hU := XGC4.UConst_pos μ κ L₀
  have hEη := XGC4.eta0_le_mean μ
  set e := eps0 μ κ L₀ with he_def
  have hinv : 0 ≤ (e ^ 2)⁻¹ := by positivity
  have hLL : L₀ + 1 < L := by
    have : ((L₀ + 1 : ℕ) : ℝ) < L := by push_cast; linarith
    exact_mod_cast this
  have hN : (e ^ 2)⁻¹ + 1 < ((L - L₀ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; linarith
  set X : ℝ := U0 μ κ L₀ * 2 ^ L₀ + eta0 μ + UConst μ κ L₀ + 1 with hX
  have hU0 : 64 * min κ.b κ.h * μ.mean ≤ U0 μ κ L₀ := by
    unfold U0
    have hmx : min κ.b κ.h ≤ max κ.b κ.h ^ 2 / min κ.b κ.h := by
      rw [le_div_iff₀ hmn]
      have : min κ.b κ.h ≤ max κ.b κ.h := min_le_max
      nlinarith
    have hm := XGT1.mean_pos μ
    have : (1 : ℝ) ≤ (L₀ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) L₀]
    have h64 : 64 * min κ.b κ.h * μ.mean ≤ 64 * (max κ.b κ.h ^ 2 / min κ.b κ.h) * μ.mean := by
      gcongr
    calc 64 * min κ.b κ.h * μ.mean ≤ 64 * (max κ.b κ.h ^ 2 / min κ.b κ.h) * μ.mean := h64
      _ ≤ 64 * ((L₀ : ℝ) + 1) * (max κ.b κ.h ^ 2 / min κ.b κ.h) * μ.mean := by
        have : 0 ≤ 64 * (max κ.b κ.h ^ 2 / min κ.b κ.h) * μ.mean := by positivity
        nlinarith
  have hU0n : 0 ≤ U0 μ κ L₀ := le_trans (by have := XGT1.mean_pos μ; positivity) hU0
  have h2L : (1 : ℝ) ≤ 2 ^ L₀ := one_le_pow₀ (by norm_num)
  have hX0 : 64 * min κ.b κ.h * μ.mean ≤ X := by
    have : U0 μ κ L₀ ≤ U0 μ κ L₀ * 2 ^ L₀ := le_mul_of_one_le_right hU0n h2L
    rw [hX]; linarith
  have hXU : UConst μ κ L₀ + 1 ≤ X := by
    have : 0 ≤ U0 μ κ L₀ * 2 ^ L₀ := by positivity
    rw [hX]; linarith
  have h1 : e ≤ 4 * (eta0 μ / 4) ^ 2 * p0hat μ ^ 2 := by
    have : e ≤ (1 / 4) * (eta0 μ * p0hat μ) ^ 2 := by
      rw [he_def]; unfold eps0; exact (min_le_right _ _).trans (min_le_left _ _)
    nlinarith
  have h2 : e * (2250000 * X ^ 2) ≤ min κ.b κ.h ^ 2 * p0hat μ ^ 2 * (eta0 μ / 4) ^ 2 := by
    have h : e ≤ (1 / 625) * c0 μ κ ^ 2 * (X ^ 2)⁻¹ := by
      rw [he_def, hX]; unfold eps0
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hX2 : 0 < X ^ 2 := pow_pos (by linarith) 2
    have : e * X ^ 2 ≤ (1 / 625) * c0 μ κ ^ 2 := by
      have := mul_le_mul_of_nonneg_right h hX2.le
      rwa [mul_assoc ((1 / 625) * c0 μ κ ^ 2), inv_mul_cancel₀ hX2.ne', mul_one] at this
    unfold c0 at this
    nlinarith
  refine XGC4.pick e (eta0 μ / 4) (UConst μ κ L₀ / min κ.b κ.h) (L - L₀) he (by positivity)
    (by positivity) hN
    (XGC4.cond_num e (eta0 μ / 4) (UConst μ κ L₀) (min κ.b κ.h) μ.mean X (p0hat μ) he he1
      (by positivity) hmn hp hp8 hU h1 h2 hXU hX0 (by linarith)) ?_
  intro m hm1 hmN
  have hk : m - 1 < L - L₀ := by omega
  have hb := XGC4.wit_bound μ κ L₀ L P χ q I D hw ⟨m - 1, hk⟩
  simp only at hb
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
    rw [Nat.cast_sub hm1]; push_cast; ring
  rw [hcast] at hb
  have hsq : Real.sqrt m ≤ Real.sqrt ((m - 1 + (L₀ + 1) : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : m ≤ m - 1 + (L₀ + 1))
  have hε : μ.mean - rL P L₀ L χ ≤ e := by linarith
  have : (m : ℝ) * (μ.mean - rL P L₀ L χ) ≤ m * e :=
    mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg _)
  have : eta0 μ / 4 * Real.sqrt m ≤ Real.sqrt ((m - 1 + (L₀ + 1) : ℕ) : ℝ) * eta0 μ / 4 := by
    nlinarith
  linarith
