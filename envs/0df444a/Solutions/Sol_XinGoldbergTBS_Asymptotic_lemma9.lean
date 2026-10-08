-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.lemma9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:00:38.02713+00:00
-- url     : https://prove2.me/submissions/4f1c78fd-2e3a-47c8-9dda-39f3cc1f2b9f

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XGL9

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

lemma core2 (e : ℝ) (he : 0 < e) (he1 : e ≤ 1 / 3200) :
    ∀ L : ℕ, (e ^ 2)⁻¹ ≤ (L : ℝ) → (e ^ 3)⁻¹ * L * Real.exp (-(e * L)) ≤ 25 := by
  intro L hL
  have hL' : 1 ≤ e ^ 2 * (L : ℝ) := by
    have := mul_le_mul_of_nonneg_left hL (sq_nonneg e)
    rwa [mul_inv_cancel₀ (by positivity)] at this
  generalize (L : ℝ) = s at hL hL' ⊢
  have hs : 0 < s := by
    by_contra h
    have : e ^ 2 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg e) (not_lt.mp h)
    linarith
  have h3 : 0 ≤ e ^ 9 * s ^ 5 := by positivity
  have hX : 3200 ≤ e ^ 9 * s ^ 5 := by
    have h1 : 1 ≤ (e ^ 2 * s) ^ 5 := one_le_pow₀ hL'
    have h2 : (e ^ 2 * s) ^ 5 = e * (e ^ 9 * s ^ 5) := by ring
    have h4 := mul_le_mul_of_nonneg_right he1 h3
    linarith
  have hexp : (e * s) ^ 6 / 720 ≤ Real.exp (e * s) := by
    have := Real.pow_div_factorial_le_exp (e * s) (by positivity) 6
    norm_num [Nat.factorial] at this
    exact this
  rw [Real.exp_neg]
  rw [show (e ^ 3)⁻¹ * s * (Real.exp (e * s))⁻¹ = s / (e ^ 3 * Real.exp (e * s)) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  have h1 : e ^ 3 * ((e * s) ^ 6 / 720) ≤ e ^ 3 * Real.exp (e * s) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have h2 : e ^ 3 * ((e * s) ^ 6 / 720) = (s * (e ^ 9 * s ^ 5)) / 720 := by ring
  have h5 : s * 3200 ≤ s * (e ^ 9 * s ^ 5) := mul_le_mul_of_nonneg_left hX hs.le
  rw [h2] at h1
  generalize s * (e ^ 9 * s ^ 5) = Y at h1 h5
  generalize e ^ 3 * Real.exp (e * s) = Z at h1 ⊢
  linarith

lemma core3 (ph K : ℝ) (hph2 : 0 < ph ^ 2) (hph8 : ph ^ 2 ≤ 1 / 8) (hKpos : 0 < K)
    (hK1' : K ≤ 1) (α : ℝ)
    (hα1 : (2 : ℝ) ^ (-(ph ^ 2) / 400) ≤ α) (hα2 : α ≤ (2 : ℝ) ^ (-K))
    (h998 : (0.998 : ℝ) < α) (hα_lt1 : α < 1) :
      (400 * (ph ^ 2)⁻¹ ≤ (mAlpha α : ℝ) ∧
        (mAlpha α : ℝ) ≤ 4 / K ∧
        400 * (ph ^ 2)⁻¹ ≤ 2 * (mAlpha α : ℝ) ∧
        2 * (mAlpha α : ℝ) ≤ 4 / K) ∧
      (1 / 4) * (1 - α)⁻¹ ≤ (mAlpha α : ℝ) ∧ (mAlpha α : ℝ) ≤ 4 * (1 - α)⁻¹ := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hαpos : 0 < α := by linarith
  have hlogneg : Real.log α < 0 := Real.log_neg hαpos hα_lt1
  have hxu : -Real.log α ≤ ph ^ 2 / 400 * Real.log 2 := by
    have := Real.log_le_log (Real.rpow_pos_of_pos (by norm_num) _) hα1
    rw [Real.log_rpow (by norm_num)] at this
    have e1 : -(ph ^ 2) / 400 * Real.log 2 = -(ph ^ 2 / 400 * Real.log 2) := by ring
    linarith
  have hxl : K * Real.log 2 ≤ -Real.log α := by
    have := Real.log_le_log hαpos hα2
    rw [Real.log_rpow (by norm_num)] at this
    have e1 : -K * Real.log 2 = -(K * Real.log 2) := by ring
    linarith
  have hx1 : 1 - α ≤ -Real.log α := by
    linarith [Real.log_le_sub_one_of_pos hαpos]
  have hx2 : α * (-Real.log α) ≤ 1 - α := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hαpos)
    rw [Real.log_inv] at this
    have h := mul_le_mul_of_nonneg_left this hαpos.le
    rw [mul_sub, mul_inv_cancel₀ hαpos.ne'] at h
    linarith
  have hr : -1 / Real.logb 2 α = Real.log 2 / (-Real.log α) := by
    rw [Real.logb]
    field_simp
  generalize hxdef : -Real.log α = x at hxu hxl hx1 hx2 hr
  have hxpos : 0 < x := by rw [← hxdef]; linarith
  have hsmall : x ≤ 1 := by
    have : ph ^ 2 / 400 * Real.log 2 ≤ ph ^ 2 / 400 :=
      mul_le_of_le_one_right (by positivity) (by linarith)
    linarith
  have hm : (mAlpha α : ℝ) = ((⌈Real.log 2 / x⌉ : ℤ) : ℝ) := by
    unfold mAlpha; rw [hr]
  rw [hm]
  have hc1 := Int.le_ceil (Real.log 2 / x)
  have hc2 := Int.ceil_lt_add_one (Real.log 2 / x)
  generalize ((⌈Real.log 2 / x⌉ : ℤ) : ℝ) = m at hc1 hc2
  have hr1 : 400 * (ph ^ 2)⁻¹ ≤ Real.log 2 / x := by
    rw [le_div_iff₀ hxpos]
    have hw : (ph ^ 2)⁻¹ * ph ^ 2 = 1 := inv_mul_cancel₀ hph2.ne'
    have hw0 : 0 ≤ (ph ^ 2)⁻¹ := by positivity
    have h := mul_le_mul_of_nonneg_left hxu hw0
    have e1 : (ph ^ 2)⁻¹ * (ph ^ 2 / 400 * Real.log 2) =
        ((ph ^ 2)⁻¹ * ph ^ 2) * Real.log 2 / 400 := by ring
    rw [e1, hw] at h
    have e2 : 400 * (ph ^ 2)⁻¹ * x = 400 * ((ph ^ 2)⁻¹ * x) := by ring
    rw [e2]; linarith
  have hr2 : Real.log 2 / x ≤ 1 / K := by
    rw [div_le_div_iff₀ hxpos hKpos]; linarith
  have hK1 : 1 ≤ 1 / K := by rw [le_div_iff₀ hKpos]; linarith
  have h4K : 4 / K = 4 * (1 / K) := by ring
  have hpinv : 0 < 400 * (ph ^ 2)⁻¹ := by positivity
  have hainv : α⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hαpos two_pos]; norm_num; linarith
  have hq : (1 / 4) * (1 - α)⁻¹ ≤ Real.log 2 / x := by
    have hi : (1 - α)⁻¹ ≤ α⁻¹ * x⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (by positivity) hx2
    calc (1 / 4) * (1 - α)⁻¹ ≤ (1 / 4) * (α⁻¹ * x⁻¹) :=
          mul_le_mul_of_nonneg_left hi (by norm_num)
      _ = ((1 / 4) * α⁻¹) * x⁻¹ := by ring
      _ ≤ Real.log 2 * x⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hxpos.le)
      _ = Real.log 2 / x := (div_eq_mul_inv _ _).symm
  have hq1 : Real.log 2 / x + 1 ≤ 4 * (1 - α)⁻¹ := by
    have a : Real.log 2 / x + 1 ≤ 4 / x := by
      rw [div_add_one hxpos.ne', div_le_div_iff_of_pos_right hxpos]; linarith
    have b : 4 / x ≤ 4 / (1 - α) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hx1
    rw [← div_eq_mul_inv]; linarith
  generalize Real.log 2 / x = r at hc1 hc2 hr1 hr2 hq hq1
  generalize 1 / K = iK at hr2 hK1 h4K
  rw [h4K]
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, by linarith, by linarith⟩

lemma core (ph η e : ℝ) (hph : 0 < ph) (hph8 : ph ^ 2 ≤ 1 / 8) (hη : 0 < η) (he : 0 < e)
    (heA : e ≤ (1 / 4) * (η * ph) ^ 2) (heB : e ≤ 1 - (2 : ℝ) ^ (-(ph ^ 2) / 400)) :
    (0.998 < (2 : ℝ) ^ (-(ph ^ 2) / 400) ∧ (2 : ℝ) ^ (-(ph ^ 2) / 400) ≤ 1 - e ∧
      1 - e ≤ (2 : ℝ) ^ (-(4 / (ph ^ 2 * η ^ 2)) * e ^ 2) ∧
        (2 : ℝ) ^ (-(4 / (ph ^ 2 * η ^ 2)) * e ^ 2) < 1) ∧
    (∀ L : ℕ, (e ^ 2)⁻¹ ≤ (L : ℝ) →
      (e ^ 3)⁻¹ * L * Real.exp (-(e * L)) ≤ 25) ∧
    (∀ α : ℝ, (2 : ℝ) ^ (-(ph ^ 2) / 400) ≤ α → α ≤ (2 : ℝ) ^ (-(4 / (ph ^ 2 * η ^ 2)) * e ^ 2) →
      (400 * (ph ^ 2)⁻¹ ≤ (mAlpha α : ℝ) ∧
        (mAlpha α : ℝ) ≤ (ph * η * e⁻¹) ^ 2 ∧
        400 * (ph ^ 2)⁻¹ ≤ 2 * (mAlpha α : ℝ) ∧
        2 * (mAlpha α : ℝ) ≤ (ph * η * e⁻¹) ^ 2) ∧
      (1 / 4) * (1 - α)⁻¹ ≤ (mAlpha α : ℝ) ∧ (mAlpha α : ℝ) ≤ 4 * (1 - α)⁻¹) := by
  have hph2 : 0 < ph ^ 2 := by positivity
  have hlow : 1 - ph ^ 2 / 400 ≤ (2 : ℝ) ^ (-(ph ^ 2) / 400) := by
    rw [neg_div]; exact two_rpow_neg_ge _ (by positivity)
  have heC : e ≤ ph ^ 2 / 400 := by linarith
  have he1 : e ≤ 1 / 3200 := by linarith
  rw [show -(4 / (ph ^ 2 * η ^ 2)) * e ^ 2 = -(4 / (ph ^ 2 * η ^ 2) * e ^ 2) by ring]
  have hph0 := hph.ne'
  have hη0 := hη.ne'
  have he0 := he.ne'
  have hK4 : (ph * η * e⁻¹) ^ 2 = 4 / (4 / (ph ^ 2 * η ^ 2) * e ^ 2) := by
    field_simp
  rw [hK4]
  have h4e : 4 * e ≤ ph ^ 2 * η ^ 2 := by
    have e1 : (1 / 4) * (η * ph) ^ 2 = ph ^ 2 * η ^ 2 / 4 := by ring
    linarith
  generalize hK : 4 / (ph ^ 2 * η ^ 2) * e ^ 2 = K
  have hKpos : 0 < K := by rw [← hK]; positivity
  have hKle : K ≤ e := by
    rw [← hK, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left h4e he.le
    have e1 : e * (4 * e) = 4 * e ^ 2 := by ring
    linarith
  have hhigh_lt : (2 : ℝ) ^ (-K) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hhigh_ge : 1 - K ≤ (2 : ℝ) ^ (-K) := two_rpow_neg_ge K hKpos.le
  have h9 : (0.998 : ℝ) < 1 - 1 / 3200 := by norm_num
  refine ⟨⟨by linarith, by linarith, by linarith, hhigh_lt⟩, core2 e he he1, ?_⟩
  intro α hα1 hα2
  exact core3 ph K hph2 hph8 hKpos (by linarith) α hα1 hα2 (by linarith)
    (lt_of_le_of_lt hα2 hhigh_lt)

end XGL9

open XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) :
    (0.998 < xiLow μ ∧ xiLow μ ≤ 1 - eps0 μ κ L₀ ∧
      1 - eps0 μ κ L₀ ≤ xiHigh μ κ L₀ ∧ xiHigh μ κ L₀ < 1) ∧
    (∀ L : ℕ, (eps0 μ κ L₀ ^ 2)⁻¹ ≤ (L : ℝ) →
      (eps0 μ κ L₀ ^ 3)⁻¹ * L * Real.exp (-(eps0 μ κ L₀ * L)) ≤ 25) ∧
    (∀ α : ℝ, xiLow μ ≤ α → α ≤ xiHigh μ κ L₀ →
      (400 * (p0hat μ ^ 2)⁻¹ ≤ (mAlpha α : ℝ) ∧
        (mAlpha α : ℝ) ≤ (p0hat μ * eta0 μ * (eps0 μ κ L₀)⁻¹) ^ 2 ∧
        400 * (p0hat μ ^ 2)⁻¹ ≤ 2 * (mAlpha α : ℝ) ∧
        2 * (mAlpha α : ℝ) ≤ (p0hat μ * eta0 μ * (eps0 μ κ L₀)⁻¹) ^ 2) ∧
      (1 / 4) * (1 - α)⁻¹ ≤ (mAlpha α : ℝ) ∧ (mAlpha α : ℝ) ≤ 4 * (1 - α)⁻¹) := by
  have hp := XGL9.p0_pos μ
  have hp1 := XGL9.p0_lt_one μ
  have hph2 : p0hat μ ^ 2 = p0 μ * (1 - p0 μ) / 2 := by
    rw [p0hat, Real.sq_sqrt (by nlinarith)]; ring
  have hph : 0 < p0hat μ := Real.sqrt_pos.mpr (by nlinarith)
  have hph8 : p0hat μ ^ 2 ≤ 1 / 8 := by rw [hph2]; nlinarith [sq_nonneg (p0 μ - 1 / 2)]
  have hη := XGL9.eta0_pos μ
  have he := XGL9.eps0_pos μ κ L₀
  have heA : eps0 μ κ L₀ ≤ (1 / 4) * (eta0 μ * p0hat μ) ^ 2 := by
    unfold eps0; exact (min_le_right _ _).trans (min_le_left _ _)
  have heB : eps0 μ κ L₀ ≤ 1 - (2 : ℝ) ^ (-(p0hat μ ^ 2) / 400) := by
    unfold eps0; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  exact XGL9.core (p0hat μ) (eta0 μ) (eps0 μ κ L₀) hph hph8 hη he heA heB
