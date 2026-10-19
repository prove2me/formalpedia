-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.tbs_asymptotically_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T15:43:03.513697+00:00
-- url     : https://prove2.me/submissions/3c3f5e34-fb2e-4ed6-88fe-5e447952a075

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_RandomWalk
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness
import Theorems.Thm_XinGoldbergTBS_Asymptotic_opt_bounds
import Theorems.Thm_XinGoldbergTBS_Asymptotic_tbs_cost_formula
import Theorems.Thm_XinGoldbergTBS_Asymptotic_stationary_witness_exists
import Theorems.Thm_XinGoldbergTBS_Asymptotic_corollary4
import Theorems.Thm_XinGoldbergTBS_Asymptotic_corollary3
import Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma5

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

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

lemma abs_sum_ge (μ : DemandLaw) (L₀ : ℕ) (x : ℝ) :
    eta0 μ ≤ ∫ y, |x - ∑ i, y i| ∂sumLaw μ L₀ := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L₀ + 1) => ℝ) 0
  have hmp : MeasurePreserving e (sumLaw μ L₀)
      (μ.law.prod (Measure.pi fun _ : Fin L₀ => μ.law)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (L₀ + 1) => μ.law) 0
  set F : ℝ × (Fin L₀ → ℝ) → ℝ := fun p => |x - (p.1 + ∑ j, p.2 j)| with hFdef
  have hF : ∀ y : Fin (L₀ + 1) → ℝ, |x - ∑ i, y i| = F (e y) := by
    intro y
    simp [hFdef, e, Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
  have hcomp : (fun y : Fin (L₀ + 1) → ℝ => |x - ∑ i, y i|) = F ∘ e := by
    funext y; exact hF y
  have hint : Integrable (fun y : Fin (L₀ + 1) → ℝ => |x - ∑ i, y i|) (sumLaw μ L₀) :=
    (integrable_shift μ L₀ x).abs
  have hFi : Integrable F (μ.law.prod (Measure.pi fun _ : Fin L₀ => μ.law)) := by
    rw [← hmp.integrable_comp_emb e.measurableEmbedding]
    rw [hcomp] at hint; exact hint
  have heq : ∫ y, |x - ∑ i, y i| ∂sumLaw μ L₀ =
      ∫ p, F p ∂(μ.law.prod (Measure.pi fun _ : Fin L₀ => μ.law)) := by
    rw [hcomp]; exact hmp.integral_comp' F
  rw [heq, integral_prod_symm F hFi]
  have hin : ∀ rest : Fin L₀ → ℝ, eta0 μ ≤ ∫ a, F (a, rest) ∂μ.law := by
    intro rest
    have h1 : (fun a => F (a, rest)) = fun a => |(x - ∑ j, rest j) - a| := by
      funext a; simp only [hFdef]; ring_nf
    rw [h1]
    refine ciInf_le ⟨0, ?_⟩ (x - ∑ j, rest j)
    rintro _ ⟨z, rfl⟩
    exact integral_nonneg fun d => abs_nonneg _
  calc eta0 μ = ∫ _rest, eta0 μ ∂(Measure.pi fun _ : Fin L₀ => μ.law) := by simp
    _ ≤ _ := integral_mono (integrable_const _) hFi.integral_prod_right hin

lemma gConst_pos (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) : 0 < gConst μ κ L₀ := by
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hη := eta0_pos μ
  have key : ∀ x : ℝ, min κ.b κ.h * eta0 μ ≤ ∫ y, G κ (x - ∑ i, y i) ∂sumLaw μ L₀ := by
    intro x
    calc min κ.b κ.h * eta0 μ ≤ min κ.b κ.h * ∫ y, |x - ∑ i, y i| ∂sumLaw μ L₀ :=
          mul_le_mul_of_nonneg_left (abs_sum_ge μ L₀ x) hm.le
      _ = ∫ y, min κ.b κ.h * |x - ∑ i, y i| ∂sumLaw μ L₀ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity)
          (integrable_G_sum μ κ L₀ x) (Eventually.of_forall fun y => G_ge κ _)
  exact lt_of_lt_of_le (mul_pos hm hη) (le_ciInf key)

lemma phi_nonneg (μ : DemandLaw) (ϵ θ : ℝ) : 0 ≤ phi μ ϵ θ :=
  mul_nonneg (Real.exp_pos _).le (integral_nonneg fun d => (Real.exp_pos _).le)

lemma gamma_le_phi (μ : DemandLaw) (ϵ θ : ℝ) (hθ : 0 ≤ θ) : gamma μ ϵ ≤ phi μ ϵ θ := by
  unfold gamma
  exact ciInf_le (f := fun t : Set.Ici (0 : ℝ) => phi μ ϵ t)
    ⟨0, by rintro _ ⟨t, rfl⟩; exact phi_nonneg _ _ _⟩ ⟨θ, hθ⟩

lemma gamma_nonneg (μ : DemandLaw) (ϵ : ℝ) : 0 ≤ gamma μ ϵ := by
  unfold gamma
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  exact le_ciInf fun t => phi_nonneg _ _ _

lemma exists_trunc (μ : DemandLaw) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧ μ.mean - δ < ∫ d, min d K ∂μ.law := by
  have ht : Tendsto (fun n : ℕ => ∫ d, min d ((n : ℝ) + 1) ∂μ.law) atTop
      (nhds (∫ d, d ∂μ.law)) := by
    refine tendsto_integral_of_dominated_convergence (fun d => |d|) (fun n => ?_)
      μ.integrable.abs (fun n => ?_) ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd (by positivity))]
      exact (min_le_left _ _).trans (le_abs_self _)
    · refine Eventually.of_forall fun d => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
      have : d ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil d).trans (Nat.cast_le.mpr hn)
        linarith
      exact (min_eq_left this).symm
  have hlt : μ.mean - δ < ∫ d, d ∂μ.law := by
    show μ.mean - δ < μ.mean; linarith
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds hlt)).exists
  exact ⟨(n : ℝ) + 1, by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)], hn⟩

lemma gamma_lt_one (μ : DemandLaw) (ϵ : ℝ) (hϵ : 0 < ϵ) : gamma μ ϵ < 1 := by
  obtain ⟨K, hK1, hK⟩ := exists_trunc μ (ϵ / 2) (by linarith)
  have hKpos : 0 < K := by linarith
  set θ := min (1 / K) (ϵ / (4 * K ^ 2)) with hθdef
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hθK : θ * K ≤ 1 := by
    have : θ ≤ 1 / K := min_le_left _ _
    calc θ * K ≤ 1 / K * K := mul_le_mul_of_nonneg_right this hKpos.le
      _ = 1 := by field_simp
  have hθ2 : θ * K ^ 2 ≤ ϵ / 4 := by
    have : θ ≤ ϵ / (4 * K ^ 2) := min_le_right _ _
    calc θ * K ^ 2 ≤ ϵ / (4 * K ^ 2) * K ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = ϵ / 4 := by field_simp
  have hpt : ∀ᵐ d ∂μ.law, Real.exp (-(θ * d)) ≤ 1 - θ * min d K + (θ * K) ^ 2 := by
    filter_upwards [ae_nonneg μ] with d hd
    have hm0 : 0 ≤ min d K := le_min hd hKpos.le
    have hu0 : 0 ≤ θ * min d K := mul_nonneg hθpos.le hm0
    have huK : θ * min d K ≤ θ * K := mul_le_mul_of_nonneg_left (min_le_right _ _) hθpos.le
    have hud : θ * min d K ≤ θ * d := mul_le_mul_of_nonneg_left (min_le_left _ _) hθpos.le
    have h1 : Real.exp (-(θ * d)) ≤ Real.exp (-(θ * min d K)) := Real.exp_le_exp.mpr (by linarith)
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -(θ * min d K))
      (by rw [abs_neg, abs_of_nonneg hu0]; linarith)
    have h3 := (abs_le.mp h2).2
    have h4 : (-(θ * min d K)) ^ 2 ≤ (θ * K) ^ 2 := by
      rw [neg_sq]; exact pow_le_pow_left₀ hu0 huK 2
    linarith
  have hint1 : Integrable (fun d => Real.exp (-(θ * d))) μ.law := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hmin : Integrable (fun d => min d K) μ.law := by
    refine Integrable.mono' (μ.integrable.abs.add (integrable_const K)) ?_ ?_
    · exact (measurable_id.min measurable_const).aestronglyMeasurable
    · filter_upwards [ae_nonneg μ] with d hd
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hd hKpos.le)]
      have := (min_le_left d K).trans (le_abs_self d)
      simp only [Pi.add_apply, id]
      linarith
  have hint2 : Integrable (fun d => 1 - θ * min d K + (θ * K) ^ 2) μ.law :=
    ((integrable_const 1).sub (hmin.const_mul θ)).add (integrable_const _)
  have hE : ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
    calc ∫ d, Real.exp (-(θ * d)) ∂μ.law ≤ ∫ d, (1 - θ * min d K + (θ * K) ^ 2) ∂μ.law :=
          integral_mono_ae hint1 hint2 hpt
      _ = 1 - θ * ∫ d, min d K ∂μ.law + (θ * K) ^ 2 := by
          rw [integral_add (f := fun d => 1 - θ * min d K) (g := fun _ => (θ * K) ^ 2)
            ((integrable_const 1).sub (hmin.const_mul θ)) (integrable_const _),
            integral_sub (f := fun _ => (1 : ℝ)) (g := fun d => θ * min d K)
              (integrable_const 1) (hmin.const_mul θ), integral_const_mul]
          simp
  have hlow : 1 - θ * (μ.mean - ϵ) ≤ Real.exp (-(θ * (μ.mean - ϵ))) := by
    linarith [Real.add_one_le_exp (-(θ * (μ.mean - ϵ)))]
  have hsq : (θ * K) ^ 2 = θ * (θ * K ^ 2) := by ring
  have hθ3 : θ * (θ * K ^ 2) ≤ θ * (ϵ / 4) := mul_le_mul_of_nonneg_left hθ2 hθpos.le
  have hK' : θ * (μ.mean - ϵ / 2) < θ * ∫ d, min d K ∂μ.law := mul_lt_mul_of_pos_left hK hθpos
  have hE' : ∫ d, Real.exp (-(θ * d)) ∂μ.law < Real.exp (-(θ * (μ.mean - ϵ))) := by
    nlinarith
  have hφ : phi μ ϵ θ < 1 := by
    unfold phi
    calc Real.exp (θ * (μ.mean - ϵ)) * ∫ d, Real.exp (-(θ * d)) ∂μ.law
        < Real.exp (θ * (μ.mean - ϵ)) * Real.exp (-(θ * (μ.mean - ϵ))) :=
          mul_lt_mul_of_pos_left hE' (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; simp
  exact lt_of_le_of_lt (gamma_le_phi μ ϵ θ hθpos.le) hφ

lemma vartheta_ne_zero (μ : DemandLaw) (ϵ : ℝ) (hγ : gamma μ ϵ < 1) : vartheta μ ϵ ≠ 0 := by
  unfold vartheta
  split_ifs with h
  · obtain ⟨θ, hθ0, hθ⟩ := h
    intro h0
    have hle : ENNReal.ofReal θ ≤ ⨆ t ∈ phiMinimizers μ ϵ, ENNReal.ofReal t :=
      le_iSup₂_of_le (f := fun t (_ : t ∈ phiMinimizers μ ϵ) => ENNReal.ofReal t) θ ⟨hθ0, hθ⟩
        le_rfl
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    have : θ = 0 := le_antisymm hle hθ0
    subst this
    have h1 : phi μ ϵ 0 = 1 := by simp [phi]
    linarith
  · exact ENNReal.top_ne_zero

/-- The numerics of Theorem 1: with `α = 1 - 4/√L`, both error terms are below `ϵ g`. -/
lemma err_numeric (u B g ϵ : ℝ) (L₀ L : ℕ) (hu : 0 ≤ u) (hB : 0 ≤ B) (hg : 0 < g)
    (hϵ : 0 < ϵ) (hL64 : 64 ≤ (L : ℝ)) (hL₀ : L₀ ≤ L)
    (hL : 25 * (g ^ 2)⁻¹ * (u * 2 ^ L₀ + B) ^ 2 * (ϵ ^ 2)⁻¹ < L) :
    ∃ α : ℝ, 1 / 2 ≤ α ∧ α < 1 ∧
      u * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀) + B * (1 - α) < ϵ * g := by
  set x := Real.sqrt (L : ℝ) with hxdef
  have hx2 : x ^ 2 = (L : ℝ) := Real.sq_sqrt (by linarith)
  have hx8 : 8 ≤ x := by
    rw [hxdef, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hxpos : 0 < x := by linarith
  set t := 4 / x with htdef
  have htpos : 0 < t := by positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [htdef, div_le_iff₀ hxpos]; linarith
  have htx : t * x = 4 := by rw [htdef]; field_simp
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  have h1a : 1 - (1 - t) = t := by ring
  rw [h1a]
  set A := u * 2 ^ L₀ + B with hA
  have hP : (0 : ℝ) < 2 ^ L₀ := by positivity
  have hu2 : 0 ≤ u * 2 ^ L₀ := mul_nonneg hu hP.le
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have key : 25 * A ^ 2 < (L : ℝ) * (g ^ 2 * ϵ ^ 2) := by
    have h := mul_lt_mul_of_pos_right hL (by positivity : (0 : ℝ) < g ^ 2 * ϵ ^ 2)
    calc 25 * A ^ 2 = 25 * (g ^ 2)⁻¹ * A ^ 2 * (ϵ ^ 2)⁻¹ * (g ^ 2 * ϵ ^ 2) := by
          field_simp
      _ < _ := h
  have h5 : 5 * A < g * ϵ * x := by
    by_contra hc
    push Not at hc
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ g * ϵ * x) hc 2
    have e1 : (g * ϵ * x) ^ 2 = x ^ 2 * (g ^ 2 * ϵ ^ 2) := by ring
    have e2 : (5 * A) ^ 2 = 25 * A ^ 2 := by ring
    rw [hx2] at e1
    linarith
  have hα0 : 0 ≤ 1 - t := by linarith
  have hpow1 : (1 - t) ^ (L - L₀) ≤ 2 ^ L₀ * (1 - t) ^ L := by
    have h2a : 1 ≤ (2 * (1 - t)) ^ L₀ := one_le_pow₀ (by linarith)
    calc (1 - t) ^ (L - L₀) ≤ (1 - t) ^ (L - L₀) * (2 * (1 - t)) ^ L₀ :=
          le_mul_of_one_le_right (pow_nonneg hα0 _) h2a
      _ = 2 ^ L₀ * ((1 - t) ^ (L - L₀) * (1 - t) ^ L₀) := by rw [mul_pow]; ring
      _ = 2 ^ L₀ * (1 - t) ^ L := by rw [pow_sub_mul_pow _ hL₀]
  have hpow2 : (1 - t) ^ L ≤ Real.exp (-(4 * x)) := by
    have hle : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    calc (1 - t) ^ L ≤ Real.exp (-t) ^ L := pow_le_pow_left₀ hα0 hle L
      _ = Real.exp ((L : ℝ) * -t) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-(4 * x)) := by
          congr 1
          rw [← hx2]
          have e : x ^ 2 * -t = -(x * (t * x)) := by ring
          rw [e, htx]; ring
  set ex := Real.exp (-(4 * x)) with hex
  have hexpos : 0 < ex := Real.exp_pos _
  have h6 : x ^ 6 * ex ≤ 1 := by
    have hf := Real.pow_div_factorial_le_exp (4 * x) (by linarith) 6
    have hfac : ((Nat.factorial 6 : ℕ) : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [hfac] at hf
    have hmul : Real.exp (4 * x) * ex = 1 := by rw [hex, ← Real.exp_add]; simp
    have e4 : (4 * x) ^ 6 = 4096 * x ^ 6 := by ring
    rw [e4] at hf
    have h7 : x ^ 6 ≤ 720 / 4096 * Real.exp (4 * x) := by linarith
    calc x ^ 6 * ex ≤ (720 / 4096 * Real.exp (4 * x)) * ex :=
          mul_le_mul_of_nonneg_right h7 hexpos.le
      _ = 720 / 4096 * (Real.exp (4 * x) * ex) := by ring
      _ = 720 / 4096 := by rw [hmul]; ring
      _ ≤ 1 := by norm_num
  have hinv : (t ^ 3)⁻¹ = x ^ 3 / 64 := by
    rw [htdef, div_pow, inv_div]; norm_num
  rw [hinv, ← hx2]
  have hE1 : u * (x ^ 3 / 64) * x ^ 2 * (1 - t) ^ (L - L₀) ≤ u * 2 ^ L₀ * (x ^ 5 * ex) / 64 := by
    have h := hpow1.trans (mul_le_mul_of_nonneg_left hpow2 hP.le)
    have hc : 0 ≤ u * (x ^ 3 / 64) * x ^ 2 := by positivity
    calc u * (x ^ 3 / 64) * x ^ 2 * (1 - t) ^ (L - L₀) ≤ u * (x ^ 3 / 64) * x ^ 2 * (2 ^ L₀ * ex) :=
          mul_le_mul_of_nonneg_left h hc
      _ = u * 2 ^ L₀ * (x ^ 5 * ex) / 64 := by ring
  have hx5 : x * (x ^ 5 * ex) ≤ 1 := by
    have e : x * (x ^ 5 * ex) = x ^ 6 * ex := by ring
    rw [e]; exact h6
  have hfinal : x * (u * 2 ^ L₀ * (x ^ 5 * ex) / 64 + B * t) ≤ 4 * A := by
    have e1 : x * (u * 2 ^ L₀ * (x ^ 5 * ex) / 64 + B * t) =
        u * 2 ^ L₀ * (x * (x ^ 5 * ex)) / 64 + B * (t * x) := by ring
    rw [e1, htx]
    have h := mul_le_mul_of_nonneg_left hx5 hu2
    linarith
  have hlt : u * 2 ^ L₀ * (x ^ 5 * ex) / 64 + B * t < ϵ * g := by
    by_contra hcon
    push Not at hcon
    have h := mul_le_mul_of_nonneg_left hcon hxpos.le
    have e : g * ϵ * x = x * (ϵ * g) := by ring
    linarith
  linarith


lemma measurable_W (r : ℝ) (i : ℕ) : Measurable (fun d : Path => W r d i) := by
  unfold W
  fun_prop

lemma measurable_Zinf (r : ℝ) : Measurable (fun d : Path => Zinf r d) := by
  unfold Zinf
  exact Measurable.iSup fun i => ENNReal.measurable_ofReal.comp (measurable_W r i)

lemma measurable_Z (r : ℝ) (k : ℕ) : Measurable (fun d : Path => Z r d k) := by
  unfold Z
  exact Measurable.iSup fun i => measurable_W r i

lemma Z_nonneg (r : ℝ) (d : Path) (k : ℕ) : 0 ≤ Z r d (k + 1) := by
  unfold Z
  have h := le_ciSup (Set.finite_range (fun i : Fin (k + 1) => W r d i)).bddAbove 0
  simpa [W] using h

lemma Z_le_Zinf (r : ℝ) (d : Path) (k : ℕ) : ENNReal.ofReal (Z r d (k + 1)) ≤ Zinf r d := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (k + 1) => W r d i)
  unfold Z
  rw [← hi]
  unfold Zinf
  exact le_iSup (fun j : ℕ => ENNReal.ofReal (W r d j)) (i : ℕ)

lemma bridge_pt (κ : Costs) (r Sα : ℝ) (L₀ : ℕ) (d : Path) (y : Fin (L₀ + 1) → ℝ) (k : ℕ) :
    (if Zinf r d = ⊤ then ⊤
      else ENNReal.ofReal (G κ ((Zinf r d).toReal + (Sα + ((L₀ : ℝ) + 1) * r) - ∑ i, y i)))
      ≤ ENNReal.ofReal (G κ (Sα + Z r d (k + 1) - ∑ i, (y i - r)))
        + ENNReal.ofReal (max κ.b κ.h) * (Zinf r d - ENNReal.ofReal (Z r d (k + 1))) := by
  have hmx : 0 < max κ.b κ.h := lt_max_of_lt_left κ.b_pos
  split_ifs with htop
  · have hne : ENNReal.ofReal (max κ.b κ.h) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hmx
    rw [htop, ENNReal.top_sub ENNReal.ofReal_ne_top, ENNReal.mul_top hne]
    simp
  · have hc0 : 0 ≤ Z r d (k + 1) := Z_nonneg r d k
    have hca : Z r d (k + 1) ≤ (Zinf r d).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal htop).mp (Z_le_Zinf r d k)
    have hsub : Zinf r d - ENNReal.ofReal (Z r d (k + 1)) =
        ENNReal.ofReal ((Zinf r d).toReal - Z r d (k + 1)) := by
      rw [ENNReal.ofReal_sub _ hc0, ENNReal.ofReal_toReal htop]
    rw [hsub, ← ENNReal.ofReal_mul hmx.le,
      ← ENNReal.ofReal_add (G_nonneg _ _) (mul_nonneg hmx.le (by linarith))]
    apply ENNReal.ofReal_le_ofReal
    have hsum : ∑ i, (y i - r) = ∑ i, y i - ((L₀ : ℝ) + 1) * r := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    rw [hsum]
    have hl := G_lip κ ((Zinf r d).toReal + (Sα + ((L₀ : ℝ) + 1) * r) - ∑ i, y i)
      (Sα + Z r d (k + 1) - (∑ i, y i - ((L₀ : ℝ) + 1) * r))
    have hin : (Zinf r d).toReal + (Sα + ((L₀ : ℝ) + 1) * r) - ∑ i, y i -
        (Sα + Z r d (k + 1) - (∑ i, y i - ((L₀ : ℝ) + 1) * r)) =
        (Zinf r d).toReal - Z r d (k + 1) := by ring
    rw [hin, abs_of_nonneg (by linarith)] at hl
    exact hl

lemma bridge_int (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (r Sα : ℝ) (k : ℕ) :
    ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
        (if Zinf r p.1 = ⊤ then ⊤
          else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + (Sα + ((L₀ : ℝ) + 1) * r) - ∑ i, p.2 i)))
        ∂((pathLaw μ).prod (sumLaw μ L₀))
      ≤ ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          ENNReal.ofReal (G κ (Sα + Z r p.1 (k + 1) - ∑ i, (p.2 i - r)))
          ∂((pathLaw μ).prod (sumLaw μ L₀))
        + ENNReal.ofReal (max κ.b κ.h) *
          ∫⁻ d, (Zinf r d - ENNReal.ofReal (Z r d (k + 1))) ∂pathLaw μ := by
  have hΔ : Measurable (fun d : Path => Zinf r d - ENNReal.ofReal (Z r d (k + 1))) :=
    (measurable_Zinf r).sub (ENNReal.measurable_ofReal.comp (measurable_Z r (k + 1)))
  have hΔp : Measurable (fun p : Path × (Fin (L₀ + 1) → ℝ) =>
      Zinf r p.1 - ENNReal.ofReal (Z r p.1 (k + 1))) := hΔ.comp measurable_fst
  calc _ ≤ ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          (ENNReal.ofReal (G κ (Sα + Z r p.1 (k + 1) - ∑ i, (p.2 i - r)))
            + ENNReal.ofReal (max κ.b κ.h) * (Zinf r p.1 - ENNReal.ofReal (Z r p.1 (k + 1))))
          ∂((pathLaw μ).prod (sumLaw μ L₀)) :=
        lintegral_mono fun p => bridge_pt κ r Sα L₀ p.1 p.2 k
    _ = _ := by
        rw [lintegral_add_right _ (hΔp.const_mul _), lintegral_const_mul _ hΔp,
          lintegral_prod _ hΔp.aemeasurable]
        simp

lemma Zinf_zero_ae (μ : DemandLaw) : ∀ᵐ d ∂pathLaw μ, Zinf 0 d = 0 := by
  have hall : ∀ᵐ d ∂pathLaw μ, ∀ j, 0 ≤ d j := by
    rw [ae_all_iff]
    intro j
    have hmp := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => μ.law) j
    unfold pathLaw
    exact ae_of_ae_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact ae_nonneg μ)
  filter_upwards [hall] with d hd
  unfold Zinf
  refine le_antisymm (iSup_le fun i => ?_) (by simp)
  refine (ENNReal.ofReal_eq_zero.mpr ?_).le
  unfold W
  exact Finset.sum_nonpos fun j _ => by linarith [hd j]

lemma tail_bound (μ : DemandLaw) (r ϵ : ℝ) (hr0 : 0 ≤ r) (hϵ : 0 < ϵ) (hϵm : ϵ < μ.mean)
    (hr : r ≤ μ.mean - ϵ) (k : ℕ) :
    ∫⁻ d, (Zinf r d - ENNReal.ofReal (Z r d (k + 1))) ∂pathLaw μ ≤
      (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ * ENNReal.ofReal (gamma μ ϵ) ^ (k + 1) := by
  rcases hr0.lt_or_eq with hpos | hzero
  · obtain ⟨-, -, -, h4⟩ := XinGoldbergTBS.Asymptotic.lemma5 μ r hpos
    obtain ⟨hfin, hb⟩ := h4 ϵ hϵ hϵm hr
    have hMle : M μ r (k + 1) ≤ Minf μ r := lintegral_mono fun d => Z_le_Zinf r d k
    have hMfin : ∫⁻ d, ENNReal.ofReal (Z r d (k + 1)) ∂pathLaw μ ≠ ⊤ :=
      ne_top_of_le_ne_top hfin.ne hMle
    have hmZ : Measurable fun d : Path => ENNReal.ofReal (Z r d (k + 1)) :=
      ENNReal.measurable_ofReal.comp (measurable_Z r (k + 1))
    rw [lintegral_sub' hmZ.aemeasurable hMfin (Eventually.of_forall fun d => Z_le_Zinf r d k)]
    exact tsub_le_iff_left.mpr (hb (k + 1) (by omega))
  · subst hzero
    calc ∫⁻ d, (Zinf 0 d - ENNReal.ofReal (Z 0 d (k + 1))) ∂pathLaw μ
        ≤ ∫⁻ d, Zinf 0 d ∂pathLaw μ := lintegral_mono fun d => tsub_le_self
      _ = 0 := by rw [lintegral_congr_ae (Zinf_zero_ae μ)]; simp
      _ ≤ _ := by simp

lemma geom_one (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) :
    ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg h0 k) (summable_geometric_of_lt_one h0 h1),
    tsum_geometric_of_lt_one h0 h1, ← ENNReal.ofReal_mul (by linarith),
    mul_inv_cancel₀ (by linarith : (1 - α) ≠ 0)]
  simp

lemma tail_sum (α γ : ℝ) (C mx : ℝ≥0∞) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∑' k : ℕ, ENNReal.ofReal (α ^ k) * (mx * (C * ENNReal.ofReal γ ^ (k + 1)))
      ≤ mx * C * (ENNReal.ofReal γ * (1 - ENNReal.ofReal γ)⁻¹) := by
  calc _ ≤ ∑' k : ℕ, mx * C * ENNReal.ofReal γ ^ (k + 1) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        have h : ENNReal.ofReal (α ^ k) ≤ 1 := ENNReal.ofReal_le_one.mpr (pow_le_one₀ hα0 hα1)
        calc ENNReal.ofReal (α ^ k) * (mx * (C * ENNReal.ofReal γ ^ (k + 1)))
            ≤ 1 * (mx * (C * ENNReal.ofReal γ ^ (k + 1))) := mul_le_mul_left h _
          _ = mx * C * ENNReal.ofReal γ ^ (k + 1) := by rw [one_mul, mul_assoc]
    _ = mx * C * ∑' k : ℕ, ENNReal.ofReal γ ^ (k + 1) := ENNReal.tsum_mul_left
    _ = _ := by rw [ENNReal.tsum_geometric_add_one]

lemma E2_eq (μ : DemandLaw) (ϵ mxr α : ℝ) (hmx : 0 ≤ mxr) (hα : 0 ≤ 1 - α)
    (hϑ : vartheta μ ϵ ≠ 0) (hγ0 : 0 ≤ gamma μ ϵ) (hγ1 : gamma μ ϵ < 1) :
    ENNReal.ofReal (1 - α) * (ENNReal.ofReal mxr * (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ *
      (ENNReal.ofReal (gamma μ ϵ) * (1 - ENNReal.ofReal (gamma μ ϵ))⁻¹))
    = ENNReal.ofReal (mxr * gamma μ ϵ * varthetaInv μ ϵ * ((1 - gamma μ ϵ) ^ 2)⁻¹ * (1 - α)) := by
  have h1γ : 0 < 1 - gamma μ ϵ := by linarith
  have hvi0 : 0 ≤ varthetaInv μ ϵ := ENNReal.toReal_nonneg
  have hvi : (vartheta μ ϵ)⁻¹ = ENNReal.ofReal (varthetaInv μ ϵ) := by
    rw [varthetaInv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hϑ)]
  have hne : ENNReal.ofReal (1 - gamma μ ϵ) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact h1γ
  have hC : (vartheta μ ϵ * ENNReal.ofReal (1 - gamma μ ϵ))⁻¹ =
      ENNReal.ofReal (varthetaInv μ ϵ * (1 - gamma μ ϵ)⁻¹) := by
    rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr hne), hvi,
      ← ENNReal.ofReal_inv_of_pos h1γ, ← ENNReal.ofReal_mul hvi0]
  have hg : 1 - ENNReal.ofReal (gamma μ ϵ) = ENNReal.ofReal (1 - gamma μ ϵ) := by
    rw [ENNReal.ofReal_sub _ hγ0, ENNReal.ofReal_one]
  have hX : 0 ≤ varthetaInv μ ϵ * (1 - gamma μ ϵ)⁻¹ := mul_nonneg hvi0 (inv_nonneg.mpr h1γ.le)
  rw [hC, hg, ← ENNReal.ofReal_inv_of_pos h1γ, ← ENNReal.ofReal_mul hγ0,
    ← ENNReal.ofReal_mul hmx, ← ENNReal.ofReal_mul (mul_nonneg hmx hX), ← ENNReal.ofReal_mul hα]
  congr 1
  field_simp

lemma final_lt (O : ℝ≥0∞) (E1 E2 ϵ g : ℝ) (hO : O ≠ ⊤) (hgO : ENNReal.ofReal g ≤ O)
    (h1 : 0 ≤ E1) (h2 : 0 ≤ E2) (hϵ : 0 < ϵ) (hlt : E1 + E2 < ϵ * g) :
    O + ENNReal.ofReal E1 + ENNReal.ofReal E2 < ENNReal.ofReal (1 + ϵ) * O := by
  have hg : 0 < ϵ * g := by linarith
  rw [add_assoc, ← ENNReal.ofReal_add h1 h2, ENNReal.ofReal_add zero_le_one hϵ.le,
    ENNReal.ofReal_one, add_mul, one_mul]
  apply ENNReal.add_lt_add_left hO
  calc ENNReal.ofReal (E1 + E2) < ENNReal.ofReal (ϵ * g) := (ENNReal.ofReal_lt_ofReal_iff hg).mpr hlt
    _ = ENNReal.ofReal ϵ * ENNReal.ofReal g := ENNReal.ofReal_mul hϵ.le
    _ ≤ ENNReal.ofReal ϵ * O := mul_le_mul_right hgO _

/-- Glue: any bound met by one TBS pair with `r ∈ [0, 𝔼D]` is met by every best pair. -/
theorem best_tbs_lt_of_witness (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (X : ℝ≥0∞)
    (hW : ∃ r ∈ Set.Icc 0 μ.mean, ∃ S : ℝ, tbsCost μ κ L₀ L r S < X) :
    ∀ r S : ℝ, IsBestTBS μ κ L₀ L r S → tbsCost μ κ L₀ L r S < X := by
  rintro r S ⟨-, hmin, hS⟩
  obtain ⟨rw, hrw, Sw, hlt⟩ := hW
  calc tbsCost μ κ L₀ L r S ≤ Finf μ κ L₀ L r := le_iInf hS
    _ ≤ Finf μ κ L₀ L rw := hmin rw hrw
    _ ≤ tbsCost μ κ L₀ L rw Sw := iInf_le _ Sw
    _ < X := hlt

theorem tbs_witness_lt (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (ϵ : ℝ)
    (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hL : (eps0 μ κ L₀ ^ 2)⁻¹ + Y0 μ κ L₀ * (ϵ ^ 2)⁻¹ < (L : ℝ)) :
    ∃ r ∈ Set.Icc 0 μ.mean, ∃ S : ℝ,
      tbsCost μ κ L₀ L r S < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L := by
  have he0 := eps0_pos μ κ L₀
  have hes := eps0_le_small μ κ L₀
  have hg := gConst_pos μ κ L₀
  have hγ0 : 0 ≤ gamma μ (eps0 μ κ L₀) := gamma_nonneg _ _
  have hγ1 : gamma μ (eps0 μ κ L₀) < 1 := gamma_lt_one _ _ he0
  have hϑ := vartheta_ne_zero μ (eps0 μ κ L₀) hγ1
  have hvi0 : 0 ≤ varthetaInv μ (eps0 μ κ L₀) := ENNReal.toReal_nonneg
  have hmx : 0 < max κ.b κ.h := lt_max_of_lt_left κ.b_pos
  have hB0 : 0 ≤ max κ.b κ.h * gamma μ (eps0 μ κ L₀) * varthetaInv μ (eps0 μ κ L₀) *
      ((1 - gamma μ (eps0 μ κ L₀)) ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hmx.le hγ0) hvi0) (inv_nonneg.mpr (by positivity))
  have hm := mean_pos μ
  have hU0 : 0 ≤ U0 μ κ L₀ := by
    unfold U0
    have hmin : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
    positivity
  set B := max κ.b κ.h * gamma μ (eps0 μ κ L₀) * varthetaInv μ (eps0 μ κ L₀) *
      ((1 - gamma μ (eps0 μ κ L₀)) ^ 2)⁻¹ with hBdef
  set A := U0 μ κ L₀ * 2 ^ L₀ + B with hAdef
  set T0 := 25 * (gConst μ κ L₀ ^ 2)⁻¹ * A ^ 2 with hT0def
  have hY : Y0 μ κ L₀ = T0 + L₀ + 1 := rfl
  have hT0 : 0 ≤ T0 := by rw [hT0def]; positivity
  set I := (ϵ ^ 2)⁻¹ with hIdef
  have hI1 : 1 ≤ I := by
    rw [hIdef]; exact (one_le_inv₀ (by positivity)).mpr (by nlinarith)
  set E := (eps0 μ κ L₀ ^ 2)⁻¹ with hEdef
  have hE : (10240000 : ℝ) ≤ E := by
    have h := inv_anti₀ (by positivity : 0 < eps0 μ κ L₀ ^ 2) (pow_le_pow_left₀ he0.le hes 2)
    have h' : ((1 / 3200 : ℝ) ^ 2)⁻¹ = 10240000 := by norm_num
    rw [h'] at h
    exact h
  rw [hY] at hL
  have hTI : 0 ≤ T0 * I := mul_nonneg hT0 (by linarith)
  have hLI : ((L₀ : ℝ) + 1) * 1 ≤ ((L₀ : ℝ) + 1) * I :=
    mul_le_mul_of_nonneg_left hI1 (by positivity)
  have hexp : (T0 + L₀ + 1) * I = T0 * I + ((L₀ : ℝ) + 1) * I := by ring
  rw [hexp] at hL
  have hLa : (L₀ : ℝ) + 1 < L := by linarith
  have hLb : (64 : ℝ) ≤ L := by linarith
  have hLc : T0 * I < L := by linarith
  have hLd' : E + L₀ + 1 < (L : ℝ) := by linarith
  have hLd : (eps0 μ κ L₀ ^ 2)⁻¹ + L₀ + 1 < (L : ℝ) := by rw [← hEdef]; exact hLd'
  have hL₀nat : L₀ + 1 < L := by exact_mod_cast hLa
  obtain ⟨Ω, mΩ, P, χ, q, I', D, hw⟩ :=
    XinGoldbergTBS.Asymptotic.stationary_witness_exists μ κ L₀ L hL₀nat
  haveI := hw.isProb
  have hr0 : 0 ≤ rL P L₀ L χ := by
    have hpos : 0 < L - L₀ - 1 := by omega
    unfold rL
    apply integral_nonneg_of_ae
    filter_upwards [hw.nonneg] with ω hω
    show (0 : ℝ) ≤ chiN L₀ L χ ω 0
    rw [chiN, dif_pos hpos]
    exact hω.1 _
  have hrlt : rL P L₀ L χ < μ.mean - eps0 μ κ L₀ :=
    XinGoldbergTBS.Asymptotic.corollary4 μ κ L₀ L P χ q I' D hw hLd
  have hrle : rL P L₀ L χ ≤ μ.mean := by linarith
  have hem : eps0 μ κ L₀ < μ.mean := by linarith
  obtain ⟨α, hα2, hα1, hnum⟩ :=
    err_numeric (U0 μ κ L₀) B (gConst μ κ L₀) ϵ L₀ L hU0 hB0 hg hϵ0 hLb (by omega) hLc
  have hα0 : 0 < α := by linarith
  set r := rL P L₀ L χ with hrdef
  set Sα := Sinf μ κ L₀ α r with hSα
  refine ⟨r, ⟨hr0, hrle⟩, Sα + ((L₀ : ℝ) + 1) * r, ?_⟩
  rw [XinGoldbergTBS.Asymptotic.tbs_cost_formula μ κ L₀ L hL₀nat r _ hr0 hrle]
  set C := (vartheta μ (eps0 μ κ L₀) * ENNReal.ofReal (1 - gamma μ (eps0 μ κ L₀)))⁻¹ with hC
  set Fint := ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
        (if Zinf r p.1 = ⊤ then ⊤
          else ENNReal.ofReal (G κ ((Zinf r p.1).toReal + (Sα + ((L₀ : ℝ) + 1) * r) - ∑ i, p.2 i)))
        ∂((pathLaw μ).prod (sumLaw μ L₀)) with hFint
  set T : ℕ → ℝ≥0∞ := fun k => ∫⁻ p : Path × (Fin (L₀ + 1) → ℝ),
          ENNReal.ofReal (G κ (Sα + Z r p.1 (k + 1) - ∑ i, (p.2 i - r)))
          ∂((pathLaw μ).prod (sumLaw μ L₀)) with hT
  have hk : ∀ k : ℕ, Fint ≤ T k +
      ENNReal.ofReal (max κ.b κ.h) * (C * ENNReal.ofReal (gamma μ (eps0 μ κ L₀)) ^ (k + 1)) :=
    fun k => (bridge_int μ κ L₀ r Sα k).trans (add_le_add_right (mul_le_mul_right
      (tail_bound μ r (eps0 μ κ L₀) hr0 he0 hem (by linarith) k) _) _)
  have hsum : Fint ≤ ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * T k +
      ENNReal.ofReal (B * (1 - α)) := by
    calc Fint = ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * Fint := by
          rw [ENNReal.tsum_mul_right, ← mul_assoc, geom_one α hα0.le hα1, one_mul]
      _ ≤ ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * (T k +
            ENNReal.ofReal (max κ.b κ.h) * (C * ENNReal.ofReal (gamma μ (eps0 μ κ L₀)) ^ (k + 1))) :=
          mul_le_mul_right (ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hk k) _) _
      _ = ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * T k +
            ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) *
              (ENNReal.ofReal (max κ.b κ.h) * (C * ENNReal.ofReal (gamma μ (eps0 μ κ L₀)) ^ (k + 1))) := by
          rw [← mul_add, ← ENNReal.tsum_add]
          congr 1
          exact tsum_congr fun k => mul_add _ _ _
      _ ≤ ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * T k +
            ENNReal.ofReal (1 - α) * (ENNReal.ofReal (max κ.b κ.h) * C *
              (ENNReal.ofReal (gamma μ (eps0 μ κ L₀)) *
                (1 - ENNReal.ofReal (gamma μ (eps0 μ κ L₀)))⁻¹)) :=
          add_le_add_right (mul_le_mul_right (tail_sum α _ C _ hα0.le hα1.le) _) _
      _ = _ := by
          rw [hC, E2_eq μ (eps0 μ κ L₀) (max κ.b κ.h) α hmx.le (by linarith) hϑ hγ0 hγ1]
  have hcor := XinGoldbergTBS.Asymptotic.corollary3 μ κ L₀ L hL₀nat P χ q I' D hw α hα0 hα1
  have hopt := XinGoldbergTBS.Asymptotic.opt_bounds μ κ L₀ L hL₀nat
  have hOtop : OPT μ κ L₀ L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hopt.2.2
  have hE1 : 0 ≤ U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀) :=
    mul_nonneg (mul_nonneg (mul_nonneg hU0 (inv_nonneg.mpr (pow_nonneg (by linarith) 3)))
      (Nat.cast_nonneg L)) (pow_nonneg hα0.le _)
  have hE2 : 0 ≤ B * (1 - α) := mul_nonneg hB0 (by linarith)
  calc ENNReal.ofReal (κ.c * (μ.mean - r)) + Fint
      ≤ ENNReal.ofReal (κ.c * (μ.mean - r)) +
          (ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * T k +
            ENNReal.ofReal (B * (1 - α))) := add_le_add_right hsum _
    _ = (ENNReal.ofReal (κ.c * (μ.mean - r)) +
          ENNReal.ofReal (1 - α) * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * T k) +
            ENNReal.ofReal (B * (1 - α)) := (add_assoc _ _ _).symm
    _ ≤ OPT μ κ L₀ L + ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) +
          ENNReal.ofReal (B * (1 - α)) := add_le_add_left hcor _
    _ < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L :=
        final_lt _ _ _ ϵ (gConst μ κ L₀) hOtop hopt.2.1 hE1 hE2 hϵ0 hnum

end XGT1

open XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (ϵ : ℝ)
    (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < 1)
    (hL : (eps0 μ κ L₀ ^ 2)⁻¹ + Y0 μ κ L₀ * (ϵ ^ 2)⁻¹ < (L : ℝ)) :
    (∃ r ∈ Set.Icc 0 μ.mean, ∃ S : ℝ,
      tbsCost μ κ L₀ L r S < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L) ∧
    ∀ r S : ℝ, IsBestTBS μ κ L₀ L r S →
      tbsCost μ κ L₀ L r S < ENNReal.ofReal (1 + ϵ) * OPT μ κ L₀ L := by
  exact ⟨XGT1.tbs_witness_lt μ κ L₀ L ϵ hϵ0 hϵ1 hL,
    XGT1.best_tbs_lt_of_witness μ κ L₀ L _ (XGT1.tbs_witness_lt μ κ L₀ L ϵ hϵ0 hϵ1 hL)⟩
