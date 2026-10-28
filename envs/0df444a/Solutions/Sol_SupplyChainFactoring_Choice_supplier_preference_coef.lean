-- Prove2me | solution 1 for SupplyChainFactoring.Choice.supplier_preference_coef
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:04:49.055282+00:00
-- url     : https://prove2.me/submissions/c64841c7-61cf-4fb8-afd6-e5a1509ae2f3

import Definitions.Def_SupplyChainFactoring_Choice_Demand
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SupplyChainFactoring_Choice_Model
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


/- Demand-analysis proofs adapted from Nickrobbins95's accepted Prove2Me submission
   af9e4247-0bc4-41ad-94af-40b390abb1b7 for the same Kouvelis–Xu demand model.
   The original uses 1 - cdf; here the bridge to the frozen tail-measure definition
   is proved explicitly, and support assumptions use DemandModel's exact fields. -/

namespace SupplyChainFactoring.Choice.Analysis
open MeasureTheory ProbabilityTheory Filter Topology

abbrev InSupport (Z : EReal) (x : ℝ) : Prop := 0 < x ∧ (x : EReal) < Z

variable (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal) (hD : DemandModel μ f Z)
include hD

lemma Fbar_eq_cdf (x : ℝ) : Fbar μ x = 1 - cdf μ x := by
  have := hD.isProbability
  change μ.real (Set.Ioi x) = 1 - cdf μ x
  rw [cdf_eq_real, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma mu_singleton (x : ℝ) : μ {x} = 0 := by
  rw [hD.hasDensity, withDensity_apply _ (measurableSet_singleton x)]
  exact setLIntegral_measure_zero _ _ (Real.volume_singleton)

lemma cdf_zero : cdf μ 0 = 0 := by
  have := hD.isProbability
  rw [cdf_eq_real, measureReal_def, ← measure_congr (Iio_ae_eq_Iic' (mu_singleton μ f Z hD 0)), hD.nonneg, ENNReal.toReal_zero]

lemma cdf_pos {x : ℝ} (hx : 0 < x) : 0 < cdf μ x := by
  have := hD.isProbability
  obtain ⟨ε0, h0, hZ⟩ := EReal.lt_iff_exists_real_btwn.mp hD.Z_pos
  have h0' : (0:ℝ) < ε0 := by exact_mod_cast h0
  have hε : 0 < min x ε0 := lt_min hx h0'
  have hsub : Set.Icc 0 (min x ε0) ⊆ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ Z} := by
    intro y hy
    refine ⟨hy.1, le_trans ?_ hZ.le⟩
    exact_mod_cast hy.2.trans (min_le_right _ _)
  obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hε.le)
    (hD.f_continuousOn.mono hsub)
  have hδ : 0 < f y0 := hD.f_pos y0 (hsub hy0).1 (hsub hy0).2
  rw [cdf_eq_real, measureReal_def]
  apply ENNReal.toReal_pos
  · rw [hD.hasDensity, withDensity_apply _ measurableSet_Iic]
    apply ne_of_gt
    calc (0:ENNReal) < ENNReal.ofReal (f y0) * volume (Set.Icc 0 (min x ε0)) := by
          simp [hδ, hx, h0']
      _ = ∫⁻ _ in Set.Icc 0 (min x ε0), ENNReal.ofReal (f y0) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ y in Set.Icc 0 (min x ε0), ENNReal.ofReal (f y) :=
          setLIntegral_mono' measurableSet_Icc (fun y hy => ENNReal.ofReal_le_ofReal (hmin hy))
      _ ≤ ∫⁻ y in Set.Iic x, ENNReal.ofReal (f y) :=
          lintegral_mono_set (fun y hy => hy.2.trans (min_le_left _ _))
  · exact measure_ne_top _ _

lemma Fbar_anti : Antitone (Fbar μ) := fun x y h => by
  simp only [Fbar_eq_cdf μ f Z hD]; linarith [monotone_cdf μ h]

lemma Fbar_le_one (x : ℝ) : (Fbar μ) x ≤ 1 := by
  simp only [Fbar_eq_cdf μ f Z hD]; linarith [cdf_nonneg μ x]

lemma Fbar_nonneg (x : ℝ) : 0 ≤ (Fbar μ) x := by
  simp only [Fbar_eq_cdf μ f Z hD]; linarith [cdf_le_one μ x]

lemma Fbar_lt_one {x : ℝ} (hx : 0 < x) : (Fbar μ) x < 1 := by
  simp only [Fbar_eq_cdf μ f Z hD]; linarith [cdf_pos μ f Z hD hx]

lemma Fbar_tendsto : Tendsto (Fbar μ) atTop (𝓝 0) := by
  have := hD.isProbability
  have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_cdf_atTop μ)
  have hF : (Fbar μ) = fun x => 1 - cdf μ x := funext (Fbar_eq_cdf μ f Z hD)
  rw [hF]; simpa using h2

lemma exists_Fbar_near_zero {r : ℝ} (hr : r < 1) : ∃ q, 0 < q ∧ r < (Fbar μ) q := by
  have hc := (cdf μ).right_continuous 0
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (1 - r) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  have h1 := h (show δ / 2 ∈ Set.Ici (0:ℝ) by simp only [Set.mem_Ici]; linarith)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  rw [cdf_zero μ f Z hD, Real.dist_eq, sub_zero] at h1
  simp only [Fbar_eq_cdf μ f Z hD]
  have := (abs_lt.mp h1).2
  linarith

lemma Fbar_ii (a b : ℝ) : IntervalIntegrable (Fbar μ) volume a b :=
  (Fbar_anti μ f Z hD).intervalIntegrable

lemma S_zero : (S μ) 0 = 0 := by simp [S]

lemma S_sub (q1 q2 : ℝ) : (S μ) q2 - (S μ) q1 = ∫ ξ in q1..q2, (Fbar μ) ξ := by
  unfold S
  rw [intervalIntegral.integral_interval_sub_left (Fbar_ii μ f Z hD _ _) (Fbar_ii μ f Z hD _ _)]

lemma S_inc_le {q1 q2 : ℝ} (h : q1 ≤ q2) : (S μ) q2 - (S μ) q1 ≤ (q2 - q1) * (Fbar μ) q1 := by
  rw [S_sub μ f Z hD]
  have := intervalIntegral.integral_mono_on h (Fbar_ii μ f Z hD q1 q2)
    (intervalIntegrable_const (c := (Fbar μ) q1)) (fun x hx => Fbar_anti μ f Z hD hx.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma S_inc_ge {q1 q2 : ℝ} (h : q1 ≤ q2) : (q2 - q1) * (Fbar μ) q2 ≤ (S μ) q2 - (S μ) q1 := by
  rw [S_sub μ f Z hD]
  have := intervalIntegral.integral_mono_on h
    (intervalIntegrable_const (c := (Fbar μ) q2)) (Fbar_ii μ f Z hD q1 q2) (fun x hx => Fbar_anti μ f Z hD hx.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma S_ge {q : ℝ} (hq : 0 ≤ q) : q * (Fbar μ) q ≤ (S μ) q := by
  have := S_inc_ge μ f Z hD hq
  rw [S_zero μ f Z hD] at this; linarith

lemma S_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ (S μ) q :=
  le_trans (mul_nonneg hq (Fbar_nonneg μ f Z hD q)) (S_ge μ f Z hD hq)

lemma S_lt {q : ℝ} (hq : 0 < q) : (S μ) q < q := by
  have h1 := S_inc_le μ f Z hD (show 0 ≤ q / 2 by linarith)
  have h2 := S_inc_le μ f Z hD (show q / 2 ≤ q by linarith)
  rw [S_zero μ f Z hD] at h1
  have h3 := Fbar_le_one μ f Z hD 0
  have h4 := Fbar_lt_one μ f Z hD (show 0 < q / 2 by linarith)
  have h5 : (q - q / 2) * (Fbar μ) (q / 2) < (q - q / 2) * 1 :=
    mul_lt_mul_of_pos_left h4 (by linarith)
  have h6 : (q / 2 - 0) * (Fbar μ) 0 ≤ (q / 2 - 0) * 1 :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  linarith

lemma S_cont : Continuous (S μ) := by
  unfold S
  exact intervalIntegral.continuous_primitive (Fbar_ii μ f Z hD) 0

lemma exists_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ q, 0 ≤ q ∧ ∀ q', 0 ≤ q' → a * (S μ) q' - b * q' ≤ a * (S μ) q - b * q := by
  have hev : ∀ᶠ Q in atTop, a * (Fbar μ) Q ≤ b ∧ 0 ≤ Q := by
    have h1 : Tendsto (fun Q => a * (Fbar μ) Q) atTop (𝓝 0) := by
      simpa using (Fbar_tendsto μ f Z hD).const_mul a
    exact (h1.eventually (ge_mem_nhds hb)).and (eventually_ge_atTop 0)
  obtain ⟨Q, hQ, hQ0⟩ := hev.exists
  have hcont : ContinuousOn (fun q => a * (S μ) q - b * q) (Set.Icc 0 Q) :=
    ((continuous_const.mul (S_cont μ f Z hD)).sub (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hQ0) hcont
  refine ⟨q, hq.1, fun q' hq' => ?_⟩
  rcases le_total q' Q with h | h
  · exact hmax ⟨hq', h⟩
  · have h1 := S_inc_le μ f Z hD h
    have h2 : a * (S μ) Q - b * Q ≤ a * (S μ) q - b * q := hmax ⟨hQ0, le_rfl⟩
    have h3 : a * ((S μ) q' - (S μ) Q) ≤ a * ((q' - Q) * (Fbar μ) Q) := mul_le_mul_of_nonneg_left h1 ha
    have h4 : (q' - Q) * (a * (Fbar μ) Q) ≤ (q' - Q) * b := mul_le_mul_of_nonneg_left hQ (by linarith)
    nlinarith

lemma exists_pos {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    ∃ q, 0 ≤ q ∧ 0 < a * (S μ) q - b * q := by
  have ha : 0 < a := by linarith
  obtain ⟨q, hq, hF⟩ := exists_Fbar_near_zero μ f Z hD (r := b / a) (by rw [div_lt_one ha]; exact hab)
  refine ⟨q, hq.le, ?_⟩
  have h1 := S_ge μ f Z hD hq.le
  have h2 : b < a * (Fbar μ) q := by rwa [div_lt_iff₀ ha, mul_comm] at hF
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le, mul_lt_mul_of_pos_left h2 hq]

lemma neg_of_le {a b q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hq : 0 < q) :
    a * (S μ) q - b * q < 0 := by
  have h1 := S_lt μ f Z hD hq
  rcases ha.eq_or_lt with h | h
  · subst h; nlinarith
  · nlinarith [mul_lt_mul_of_pos_left h1 h, mul_le_mul_of_nonneg_right hab hq.le]

lemma cdf_cont : Continuous (cdf μ) := by
  have := hD.isProbability
  rw [continuous_iff_continuousAt]; intro x
  rw [(cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, mu_singleton μ f Z hD] at h
  have h2 := (cdf μ).mono.leftLim_le (le_refl x)
  have h3 : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 := ENNReal.ofReal_eq_zero.mp h.symm
  linarith

lemma Fbar_cont : Continuous (Fbar μ) :=
  by
    simpa only [show (Fbar μ) = (fun x => 1 - cdf μ x) from funext (Fbar_eq_cdf μ f Z hD)] using (show Continuous (fun x => 1 - cdf μ x) from continuous_const.sub (cdf_cont μ f Z hD))

lemma Fbar_eq_zero {q : ℝ} (hq : Z ≤ (q : EReal)) : Fbar μ q = 0 := by
  rw [Fbar, hD.support_le q hq, ENNReal.toReal_zero]

lemma cdf_eq_int {z1 y : ℝ} (hz1 : (z1 : EReal) ≤ Z) (hy0 : 0 ≤ y) (hy1 : y ≤ z1) :
    cdf μ y = ∫ t in (0:ℝ)..y, f t := by
  have := hD.isProbability
  have hcont : ContinuousOn f (Set.Icc 0 y) := hD.f_continuousOn.mono (fun t ht =>
    ⟨ht.1, le_trans (by exact_mod_cast ht.2.trans hy1) hz1⟩)
  have hint : IntegrableOn f (Set.Ioc 0 y) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have h1 : μ (Set.Ioc 0 y) = ENNReal.ofReal (cdf μ y - cdf μ 0) := by
    rw [← (cdf μ).measure_Ioc, measure_cdf]
  have h2 : μ (Set.Ioc 0 y) = ENNReal.ofReal (∫ t in Set.Ioc 0 y, f t) := by
    rw [hD.hasDensity, withDensity_apply _ measurableSet_Ioc,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun t => by simpa using hD.f_nonneg t))]
  rw [h1, cdf_zero μ f Z hD, sub_zero] at h2
  rw [intervalIntegral.integral_of_le hy0]
  have hnn : 0 ≤ ∫ t in Set.Ioc 0 y, f t :=
    setIntegral_nonneg measurableSet_Ioc (fun t _ => hD.f_nonneg t)
  exact (ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) hnn).mp h2

lemma cdf_hasDerivAt {x : ℝ} (hx : InSupport Z x) : HasDerivAt (cdf μ) (f x) x := by
  obtain ⟨z1, hxz, hz1⟩ := EReal.lt_iff_exists_real_btwn.mp hx.2
  have hxz' : x < z1 := by exact_mod_cast hxz
  have hcont : ContinuousOn f (Set.Icc 0 z1) := hD.f_continuousOn.mono (fun t ht =>
    ⟨ht.1, le_trans (by exact_mod_cast ht.2) hz1.le⟩)
  have hI : IntervalIntegrable f volume 0 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1.le (hcont.mono (Set.Icc_subset_Icc_right hxz'.le))
  have hO : Set.Ioo 0 z1 ∈ 𝓝 x := Ioo_mem_nhds hx.1 hxz'
  have hmeas : StronglyMeasurableAtFilter f (𝓝 x) :=
    (hcont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x ⟨hx.1, hxz'⟩
  have hca : ContinuousAt f x := hcont.continuousAt (Icc_mem_nhds hx.1 hxz')
  have hd := intervalIntegral.integral_hasDerivAt_right hI hmeas hca
  apply hd.congr_of_eventuallyEq
  filter_upwards [hO] with y hy
  exact cdf_eq_int μ f Z hD hz1.le hy.1.le hy.2.le

lemma Fbar_hasDerivAt {x : ℝ} (hx : InSupport Z x) : HasDerivAt (Fbar μ) (-f x) x :=
  by
    simpa only [show (Fbar μ) = (fun x => 1 - cdf μ x) from funext (Fbar_eq_cdf μ f Z hD)] using (cdf_hasDerivAt μ f Z hD hx).const_sub 1

lemma Fbar_strict {x y : ℝ} (hx : InSupport Z x) (hy : InSupport Z y) (h : x < y) :
    (Fbar μ) y < (Fbar μ) x := by
  have hsub : ∀ t ∈ Set.Icc x y, InSupport Z t := fun t ht =>
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt (by exact_mod_cast ht.2) hy.2⟩
  have := strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc x y) (f' := fun t => -f t)
    (Fbar_cont μ f Z hD).continuousOn
    (fun t ht => (Fbar_hasDerivAt μ f Z hD (hsub t (interior_subset ht))).hasDerivWithinAt)
    (fun t ht => by
      have := hD.f_pos t (hsub t (interior_subset ht)).1.le (hsub t (interior_subset ht)).2.le
      linarith)
  exact this ⟨le_refl x, h.le⟩ ⟨h.le, le_refl y⟩ h

lemma S_hasDerivAt (x : ℝ) : HasDerivAt (S μ) ((Fbar μ) x) x :=
  show HasDerivAt (fun u => ∫ ξ in (0:ℝ)..u, (Fbar μ) ξ) ((Fbar μ) x) x from
    intervalIntegral.integral_hasDerivAt_right (Fbar_ii μ f Z hD 0 x)
      ((Fbar_cont μ f Z hD).stronglyMeasurableAtFilter _ _) (Fbar_cont μ f Z hD).continuousAt

lemma focn {a b q : ℝ} (hb : 0 < b) (hab : b < a) (hq : 0 ≤ q)
    (hmax : ∀ q', 0 ≤ q' → a * (S μ) q' - b * q' ≤ a * (S μ) q - b * q) :
    InSupport Z q ∧ a * (Fbar μ) q = b := by
  have ha : 0 < a := by linarith
  obtain ⟨q1, hq1, hp1⟩ := exists_pos μ f Z hD hb hab
  have hgq : 0 < a * (S μ) q - b * q := lt_of_lt_of_le hp1 (hmax q1 hq1)
  have hq0 : 0 < q := by
    rcases hq.eq_or_lt with h | h
    · rw [← h, S_zero μ f Z hD] at hgq; simp at hgq
    · exact h
  have hcont : Continuous (fun y => a * (Fbar μ) y) := continuous_const.mul (Fbar_cont μ f Z hD)
  have hR : a * (Fbar μ) q ≤ b := by
    have ht : Tendsto (fun y => a * (Fbar μ) y) (𝓝[>] q) (𝓝 (a * (Fbar μ) q)) :=
      (hcont.tendsto q).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : q < y := hy
    have h1 := hmax y (by linarith)
    have h2 := mul_le_mul_of_nonneg_left (S_inc_ge μ f Z hD hy'.le) ha.le
    have h3 : (y - q) * (a * (Fbar μ) y) ≤ (y - q) * b := by nlinarith
    exact le_of_mul_le_mul_left h3 (by linarith)
  have hL : b ≤ a * (Fbar μ) q := by
    have ht : Tendsto (fun y => a * (Fbar μ) y) (𝓝[<] q) (𝓝 (a * (Fbar μ) q)) :=
      (hcont.tendsto q).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT hq0] with y hy
    have h1 := hmax y hy.1.le
    have h2 := mul_le_mul_of_nonneg_left (S_inc_le μ f Z hD hy.2.le) ha.le
    have h3 : (q - y) * b ≤ (q - y) * (a * (Fbar μ) y) := by nlinarith
    exact le_of_mul_le_mul_left h3 (by linarith [hy.2])
  have heq : a * (Fbar μ) q = b := le_antisymm hR hL
  refine ⟨⟨hq0, ?_⟩, heq⟩
  by_contra hZ
  rw [Fbar_eq_zero μ f Z hD (not_lt.mp hZ)] at heq
  linarith


lemma Fbar_pos {x : ℝ} (hx : InSupport Z x) : 0 < (Fbar μ) x := by
  obtain ⟨z1, hxz, hz1⟩ := EReal.lt_iff_exists_real_btwn.mp hx.2
  have hxz' : x < z1 := by exact_mod_cast hxz
  have h := Fbar_strict μ f Z hD hx ⟨lt_trans hx.1 hxz', hz1⟩ hxz'
  linarith [Fbar_nonneg μ f Z hD z1]

lemma S_mono {x y : ℝ} (h : x ≤ y) : (S μ) x ≤ (S μ) y := by
  have := S_inc_ge μ f Z hD h
  nlinarith [Fbar_nonneg μ f Z hD y]

lemma kz_mono {x y : ℝ} (hx : InSupport Z x) (hy : InSupport Z y) (h : x ≤ y) :
    (k μ) x * (z μ f) x ≤ (k μ) y * (z μ f) y := by
  have hFx := Fbar_pos μ f Z hD hx
  have hFy := Fbar_pos μ f Z hD hy
  have hk : (k μ) x ≤ (k μ) y := by
    unfold k
    rw [div_le_div_iff₀ hFx hFy]
    have h1 := S_mono μ f Z hD h
    have h2 := Fbar_anti μ f Z hD h
    have h3 := S_nonneg μ f Z hD hx.1.le
    nlinarith
  have hz : (z μ f) x ≤ (z μ f) y := by
    have hmem : ∀ t, InSupport Z t → t ∈ {x : ℝ | 0 ≤ x ∧ (x : EReal) < Z} :=
      fun t ht => ⟨ht.1.le, ht.2⟩
    exact hD.strictIFR.monotoneOn (hmem x hx) (hmem y hy) h
  have hz0 : 0 ≤ (z μ f) x := div_nonneg (hD.f_nonneg x) hFx.le
  have hk0 : 0 ≤ (k μ) y := div_nonneg (S_nonneg μ f Z hD hy.1.le) hFy.le
  exact mul_le_mul hk hz hz0 hk0


lemma Fbar_zero : Fbar μ 0 = 1 := by
  rw [Fbar_eq_cdf μ f Z hD, cdf_zero μ f Z hD, sub_zero]

lemma max_of_foc {a b q : ℝ} (ha : 0 ≤ a) (hfoc : a * Fbar μ q = b) :
    ∀ q' : ℝ, 0 ≤ q' → a * S μ q' - b * q' ≤ a * S μ q - b * q := by
  intro q' _
  rcases le_total q q' with h | h
  · have hS := mul_le_mul_of_nonneg_left (S_inc_le μ f Z hD h) ha
    nlinarith [hfoc]
  · have hS := mul_le_mul_of_nonneg_left (S_inc_ge μ f Z hD h) ha
    nlinarith [hfoc]

lemma neg_of_le_any {a b q : ℝ} (hab : a ≤ b) (hb : 0 < b) (hq : 0 < q) :
    a * S μ q - b * q < 0 := by
  by_cases ha : 0 ≤ a
  · exact neg_of_le μ f Z hD ha hab hb hq
  · have hS := S_nonneg μ f Z hD hq.le
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ha) hS
    nlinarith [mul_pos hb hq]

lemma S_pos {q : ℝ} (hq : InSupport Z q) : 0 < S μ q :=
  (mul_pos hq.1 (Fbar_pos μ f Z hD hq)).trans_le (S_ge μ f Z hD hq.1.le)

lemma k_sub_id_strict {x y : ℝ} (hx : InSupport Z x) (hy : InSupport Z y) (hxy : x < y) :
    k μ x - x < k μ y - y := by
  have hFx := Fbar_pos μ f Z hD hx
  have hFy := Fbar_pos μ f Z hD hy
  have hF := Fbar_strict μ f Z hD hx hy hxy
  have hSx := S_pos μ f Z hD hx
  have hS := S_inc_ge μ f Z hD hxy.le
  have hsplit : S μ x / Fbar μ y + (y - x) ≤ S μ y / Fbar μ y := by
    apply (le_div_iff₀ hFy).mpr
    have he : (S μ x / Fbar μ y + (y - x)) * Fbar μ y =
        S μ x + (y - x) * Fbar μ y := by
      rw [add_mul, div_mul_cancel₀ _ hFy.ne']
    rw [he]
    linarith
  have hstrict : S μ x / Fbar μ x < S μ x / Fbar μ y :=
    (div_lt_div_iff_of_pos_left hSx hFx hFy).mpr hF
  unfold k
  linarith

end SupplyChainFactoring.Choice.Analysis


namespace SupplyChainFactoring.Choice.Analysis
open MeasureTheory Real Filter Topology

variable (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal) (hD : DemandModel μ f Z)
include hD

lemma generic_feasible_iff (A B K L p : ℝ) (hB : 0 < B) (hK : 0 < K)
    (hL : 0 < L) (hp : 0 < p) :
    (∃ w q : ℝ, 0 ≤ w ∧ 0 ≤ q ∧
      (∀ q' : ℝ, 0 ≤ q' → K * (A * w * S μ q' - B * q') ≤ K * (A * w * S μ q - B * q)) ∧
      0 < L * (p - w) * S μ q) ↔ B < A * p := by
  constructor
  · rintro ⟨w, q, hw, hq, hbr, hret⟩
    have hS := S_nonneg μ f Z hD hq
    have hcore : 0 < (p - w) * S μ q := by
      exact (mul_pos_iff_of_pos_left hL).mp (by simpa only [mul_assoc] using hret)
    have hwp : w < p := by
      have hh := pos_of_mul_pos_left hcore hS
      linarith
    have hqp : 0 < q := by
      rcases hq.eq_or_lt with h | h
      · rw [← h, S_zero μ f Z hD] at hcore
        simp at hcore
      · exact h
    have h0 := hbr 0 (le_refl 0)
    simp only [S_zero μ f Z hD, mul_zero, sub_self] at h0
    have hinner : 0 ≤ A * w * S μ q - B * q :=
      (mul_nonneg_iff_of_pos_left hK).mp h0
    have hBAw : B < A * w := by
      by_contra hn
      exact (not_lt_of_ge hinner) (neg_of_le_any μ f Z hD (le_of_not_gt hn) hB hqp)
    have hA : 0 < A := pos_of_mul_pos_left (hB.trans hBAw) hw
    exact hBAw.trans (mul_lt_mul_of_pos_left hwp hA)
  · intro hBAp
    have hA : 0 < A := pos_of_mul_pos_left (hB.trans hBAp) hp.le
    let w : ℝ := (B / A + p) / 2
    have hdp : B / A < p := (div_lt_iff₀ hA).mpr (by simpa only [mul_comm] using hBAp)
    have hd : 0 < B / A := div_pos hB hA
    have hw : 0 < w := by dsimp [w]; linarith
    have hwp : w < p := by dsimp [w]; linarith
    have hdw : B / A < w := by dsimp [w]; linarith
    have hBAw : B < A * w := by
      simpa only [mul_comm] using (div_lt_iff₀ hA).mp hdw
    obtain ⟨q, hq, hmax⟩ := exists_max μ f Z hD (a := A * w) (mul_pos hA hw).le hB
    obtain ⟨q₁, hq₁, hprofit⟩ := exists_pos μ f Z hD hB hBAw
    have hprofitq : 0 < A * w * S μ q - B * q := hprofit.trans_le (hmax q₁ hq₁)
    have hSq : 0 < S μ q := by
      have hproduct : 0 < A * w * S μ q := by
        have := mul_nonneg hB.le hq
        linarith
      exact pos_of_mul_pos_right hproduct (mul_pos hA hw).le
    refine ⟨w, q, hw.le, hq, ?_, ?_⟩
    · intro q' hq'
      exact mul_le_mul_of_nonneg_left (hmax q' hq') hK.le
    · exact mul_pos (mul_pos hL (sub_pos.mpr hwp)) hSq

lemma rho_survival_pos (P : Params) (hP : P.Valid) {C : ℝ}
    (hC : C ∈ Set.Ioo P.Cmin P.Cmax) : 0 < 1 - P.ρ C := by
  obtain ⟨a, ha, haC⟩ := exists_between hC.1
  have hh := lt_of_lt_of_le (hP.ρ_strictAnti ⟨ha, haC.trans hC.2⟩ hC haC)
    (hP.ρ_mem a ⟨ha, haC.trans hC.2⟩).2
  exact sub_pos.mpr hh

lemma retailer_factor_pos (P : Params) (hP : P.Valid) (i : Scheme) {τ : ℝ}
    (hτ : 0 ≤ τ) : 0 < retailerFactor P i τ := by
  cases i with
  | recourse => norm_num [retailerFactor]
  | nonRecourse => norm_num [retailerFactor]
  | reverse =>
    have hh : exp (-(P.lamR * τ)) ≤ 1 :=
      exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hP.lamR_nonneg hτ))
    dsimp [retailerFactor]
    linarith

lemma feasible_iff_budget (P : Params) (hP : P.Valid) (i : Scheme) {Cs Cr τ : ℝ}
    (hCs : Cs ∈ Set.Ioo P.Cmin P.Cmax) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (hτ : 0 ≤ τ) :
    Feasible P μ i Cs Cr τ ↔
      P.c * exp ((P.η Cs + P.lamS) * P.t1) < P.p * coef P i Cs Cr τ := by
  let A := coef P i Cs Cr τ * exp (-(P.lamS * P.t1))
  let B := P.c * exp (P.η Cs * P.t1)
  let K := 1 - P.ρ Cs
  let L := exp (-(P.lamS * P.t1)) * (1 - P.ρ Cr) * retailerFactor P i τ
  have hB : 0 < B := mul_pos hP.c_pos (exp_pos _)
  have hK : 0 < K := rho_survival_pos μ f Z hD P hP hCs
  have hL : 0 < L := mul_pos
    (mul_pos (exp_pos _) (rho_survival_pos μ f Z hD P hP hCr))
    (retailer_factor_pos μ f Z hD P hP i hτ)
  have hh := generic_feasible_iff μ f Z hD A B K L P.p hB hK hL
    (hP.c_pos.trans hP.c_lt_p)
  have hscaled : Feasible P μ i Cs Cr τ ↔ B < A * P.p := by
    simpa only [Feasible, IsBestResponse, supplierProfit, retailerProfit, A, B, K, L,
      mul_assoc, mul_left_comm, mul_comm, and_assoc] using hh
  rw [hscaled]
  have hcost : B = (P.c * exp ((P.η Cs + P.lamS) * P.t1)) * exp (-(P.lamS * P.t1)) := by
    dsimp [B]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  have hrev : A * P.p = (P.p * coef P i Cs Cr τ) * exp (-(P.lamS * P.t1)) := by
    dsimp [A]
    ring
  rw [hcost, hrev]
  exact mul_lt_mul_iff_left₀ (exp_pos _)

lemma generic_best_response_iff (a b q : ℝ) (hb : 0 < b) :
    (0 ≤ q ∧ ∀ q' : ℝ, 0 ≤ q' → a * S μ q' - b * q' ≤ a * S μ q - b * q) ↔
    (a ≤ b ∧ q = 0) ∨ (b < a ∧ InSupport Z q ∧ a * Fbar μ q = b) := by
  constructor
  · rintro ⟨hq, hmax⟩
    rcases le_or_gt a b with hab | hba
    · refine Or.inl ⟨hab, ?_⟩
      by_contra hq0
      have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      have hh := hmax 0 (le_refl 0)
      simp only [S_zero μ f Z hD, mul_zero, sub_self] at hh
      exact (not_lt_of_ge hh) (neg_of_le_any μ f Z hD hab hb hqp)
    · exact Or.inr ⟨hba, focn μ f Z hD hb hba hq hmax⟩
  · rintro (⟨hab, rfl⟩ | ⟨hba, hq, hfoc⟩)
    · refine ⟨le_refl 0, fun q' hq' => ?_⟩
      simp only [S_zero μ f Z hD, mul_zero, sub_self]
      rcases hq'.eq_or_lt with he | hqpos
      · rw [← he, S_zero μ f Z hD]
        simp
      · exact (neg_of_le_any μ f Z hD hab hb hqpos).le
    · exact ⟨hq.1.le, max_of_foc μ f Z hD (hb.trans hba).le hfoc⟩

lemma retailer_objective_deriv (p d : ℝ) {q : ℝ} (hq : InSupport Z q) :
    HasDerivAt (fun x => (p - d / Fbar μ x) * S μ x)
      (p * Fbar μ q - d * (1 + z μ f q * k μ q)) q := by
  have hF := Fbar_hasDerivAt μ f Z hD hq
  have hS := S_hasDerivAt μ f Z hD q
  have hne := (Fbar_pos μ f Z hD hq).ne'
  have hd := ((hasDerivAt_const q p).sub ((hasDerivAt_const q d).div hF hne)).mul hS
  convert hd using 1 <;> try rfl
  simp only [Pi.sub_apply, Pi.div_apply, Pi.mul_apply]
  unfold z k
  field_simp [hne]
  <;> ring

lemma equilibrium_foc (P : Params) (hP : P.Valid) (i : Scheme) {Cs Cr τ w q : ℝ}
    (hCs : Cs ∈ Set.Ioo P.Cmin P.Cmax) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (hτ : 0 ≤ τ) (hfeas : Feasible P μ i Cs Cr τ)
    (heq : IsEquilibrium P μ i Cs Cr τ w q) :
    InSupport Z q ∧ 0 < coef P i Cs Cr τ ∧
    w * Fbar μ q = (P.c * exp (P.η Cs * P.t1)) /
      (coef P i Cs Cr τ * exp (-(P.lamS * P.t1))) ∧
    P.p * Fbar μ q = ((P.c * exp (P.η Cs * P.t1)) /
      (coef P i Cs Cr τ * exp (-(P.lamS * P.t1)))) * (1 + z μ f q * k μ q) := by
  let A := coef P i Cs Cr τ * exp (-(P.lamS * P.t1))
  let B := P.c * exp (P.η Cs * P.t1)
  let K := 1 - P.ρ Cs
  let L := exp (-(P.lamS * P.t1)) * (1 - P.ρ Cr) * retailerFactor P i τ
  have hB : 0 < B := mul_pos hP.c_pos (exp_pos _)
  have hK : 0 < K := rho_survival_pos μ f Z hD P hP hCs
  have hL : 0 < L := mul_pos
    (mul_pos (exp_pos _) (rho_survival_pos μ f Z hD P hP hCr))
    (retailer_factor_pos μ f Z hD P hP i hτ)
  have hsupp : ∀ u x, supplierProfit P μ i Cs Cr τ u x = K * (A * u * S μ x - B * x) := by
    intro u x
    dsimp [supplierProfit, K, A, B]
    ring
  have hret : ∀ u x, retailerProfit P μ i Cr τ u x = L * ((P.p - u) * S μ x) := by
    intro u x
    dsimp [retailerProfit, L]
    ring
  have hbr : ∀ u x, IsBestResponse P μ i Cs Cr τ u x ↔
      0 ≤ x ∧ ∀ y, 0 ≤ y → A * u * S μ y - B * y ≤ A * u * S μ x - B * x := by
    intro u x
    simp only [IsBestResponse, hsupp, mul_le_mul_iff_right₀ hK]
  obtain ⟨w₀, q₀, hw₀, hbr₀, hpos₀⟩ := hfeas
  have hpos := hpos₀.trans_le (heq.2.2 w₀ q₀ hw₀ hbr₀)
  rw [hret] at hpos
  have hcore : 0 < (P.p - w) * S μ q := (mul_pos_iff_of_pos_left hL).mp hpos
  obtain ⟨hq, hmax⟩ := (hbr w q).mp heq.2.1
  have hqp : 0 < q := by
    rcases hq.eq_or_lt with h | h
    · rw [← h, S_zero μ f Z hD] at hcore
      simp at hcore
    · exact h
  have h0 := hmax 0 (le_refl 0)
  simp only [S_zero μ f Z hD, mul_zero, sub_self] at h0
  have hBAw : B < A * w := by
    by_contra hn
    exact (not_lt_of_ge h0) (neg_of_le_any μ f Z hD (le_of_not_gt hn) hB hqp)
  have hA : 0 < A := pos_of_mul_pos_left (hB.trans hBAw) heq.1
  have hcoef : 0 < coef P i Cs Cr τ := pos_of_mul_pos_left hA (exp_pos _).le
  obtain ⟨hqSupport, hfoc⟩ := focn μ f Z hD hB hBAw hq hmax
  have hF := Fbar_pos μ f Z hD hqSupport
  have hqfoc : w * Fbar μ q = B / A := by
    apply (eq_div_iff hA.ne').mpr
    nlinarith [hfoc]
  have hwfoc : w = (B / A) / Fbar μ q := (eq_div_iff hF.ne').mpr hqfoc
  refine ⟨hqSupport, hcoef, hqfoc, ?_⟩
  have hlocal : IsLocalMax (fun x => (P.p - (B / A) / Fbar μ x) * S μ x) q := by
    change ∀ᶠ x in 𝓝 q,
      (P.p - (B / A) / Fbar μ x) * S μ x ≤ (P.p - (B / A) / Fbar μ q) * S μ q
    have hFnear : ∀ᶠ x in 𝓝 q, 0 < Fbar μ x :=
      (Fbar_cont μ f Z hD).continuousAt.eventually (Ioi_mem_nhds hF)
    filter_upwards [Ioi_mem_nhds hqp, hFnear] with x hx hxF
    let u := (B / A) / Fbar μ x
    have hu : 0 ≤ u := (div_pos (div_pos hB hA) hxF).le
    have hufoc : A * u * Fbar μ x = B := by
      dsimp [u]
      field_simp [hA.ne', hxF.ne']
    have hbrx := (hbr u x).mpr ⟨hx.le,
      max_of_foc μ f Z hD (mul_nonneg hA.le hu) hufoc⟩
    have hh := heq.2.2 u x hu hbrx
    rw [hret, hret] at hh
    have hh := (mul_le_mul_iff_right₀ hL).mp hh
    simpa only [hwfoc] using hh
  have hzero := hlocal.hasDerivAt_eq_zero (retailer_objective_deriv μ f Z hD P.p (B / A) hqSupport)
  exact sub_eq_zero.mp hzero

lemma equilibrium_ratio_strict :
    StrictMonoOn (fun q => (1 + z μ f q * k μ q) / Fbar μ q) {q | InSupport Z q} := by
  intro x hx y hy hxy
  have hFx := Fbar_pos μ f Z hD hx
  have hFy := Fbar_pos μ f Z hD hy
  have hF := Fbar_strict μ f Z hD hx hy hxy
  have ht : z μ f x * k μ x ≤ z μ f y * k μ y := by
    simpa only [mul_comm] using kz_mono μ f Z hD hx hy hxy.le
  have ht0 : 0 ≤ z μ f x * k μ x :=
    mul_nonneg (div_nonneg (hD.f_nonneg x) hFx.le)
      (div_nonneg (S_nonneg μ f Z hD hx.1.le) hFx.le)
  apply (div_lt_div_iff₀ hFx hFy).mpr
  exact (mul_lt_mul_of_pos_left hF (by linarith : 0 < 1 + z μ f x * k μ x)).trans_le
    (mul_le_mul_of_nonneg_right (by linarith :
      1 + z μ f x * k μ x ≤ 1 + z μ f y * k μ y) hFx.le)

lemma coefficient_of_foc {a e p b F t : ℝ} (ha : 0 < a) (he : 0 < e)
    (hp : 0 < p) (hF : 0 < F)
    (hfoc : p * F = (b / (a * e)) * (1 + t)) :
    a = (b / (e * p)) * ((1 + t) / F) := by
  have hh : (p * F) * (a * e) = b * (1 + t) :=
    (eq_div_iff (mul_pos ha he).ne').mp (by
      simpa only [div_mul_eq_mul_div] using hfoc)
  field_simp [he.ne', hp.ne', hF.ne']
  nlinarith [hh]

lemma supplier_profit_of_equilibrium_foc (P : Params) (i : Scheme) (Cs Cr τ w q : ℝ)
    (hcoef : 0 < coef P i Cs Cr τ) (hF : 0 < Fbar μ q)
    (hfoc : w * Fbar μ q = (P.c * exp (P.η Cs * P.t1)) /
      (coef P i Cs Cr τ * exp (-(P.lamS * P.t1)))) :
    supplierProfit P μ i Cs Cr τ w q =
      ((1 - P.ρ Cs) * (P.c * exp (P.η Cs * P.t1))) * (k μ q - q) := by
  let A := coef P i Cs Cr τ * exp (-(P.lamS * P.t1))
  let B := P.c * exp (P.η Cs * P.t1)
  have hA : 0 < A := mul_pos hcoef (exp_pos _)
  have hAw : A * w = B / Fbar μ q := by
    apply (eq_div_iff hF.ne').mpr
    calc A * w * Fbar μ q = (w * Fbar μ q) * A := by ring
      _ = (B / A) * A := by rw [hfoc]
      _ = B := div_mul_cancel₀ _ hA.ne'
  have hsupp : supplierProfit P μ i Cs Cr τ w q =
      (1 - P.ρ Cs) * (A * w * S μ q - B * q) := by
    dsimp [supplierProfit, A, B]
    ring
  rw [hsupp, hAw]
  dsimp [B, k]
  simp only [div_eq_mul_inv]
  ring

end SupplyChainFactoring.Choice.Analysis


open MeasureTheory Real SupplyChainFactoring.Choice SupplyChainFactoring.Choice.Analysis

theorem solution (P : Params) (hP : P.Valid) (μ : Measure ℝ) (f : ℝ → ℝ) (Z : EReal)
    (hD : DemandModel μ f Z) (Cr : ℝ) (hCr : Cr ∈ Set.Ioo P.Cmin P.Cmax)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ Cs ∈ Set.Ioo P.Cmin P.Cmax, ∀ i j : Scheme,
      Feasible P μ i Cs Cr τ → Feasible P μ j Cs Cr τ →
      ∀ wi qi wj qj : ℝ, IsEquilibrium P μ i Cs Cr τ wi qi → IsEquilibrium P μ j Cs Cr τ wj qj →
        (supplierProfit P μ i Cs Cr τ wi qi ≤ supplierProfit P μ j Cs Cr τ wj qj ↔
            coef P i Cs Cr τ ≤ coef P j Cs Cr τ) ∧
        (supplierProfit P μ i Cs Cr τ wi qi < supplierProfit P μ j Cs Cr τ wj qj ↔
            coef P i Cs Cr τ < coef P j Cs Cr τ) := by
  intro Cs hCs i j hfeasi hfeasj wi qi wj qj heqi heqj
  obtain ⟨hqi, hci, hwFi, hFi⟩ := equilibrium_foc μ f Z hD P hP i hCs hCr hτ hfeasi heqi
  obtain ⟨hqj, hcj, hwFj, hFj⟩ := equilibrium_foc μ f Z hD P hP j hCs hCr hτ hfeasj heqj
  have hp : 0 < P.p := hP.c_pos.trans hP.c_lt_p
  have hFqi := Fbar_pos μ f Z hD hqi
  have hFqj := Fbar_pos μ f Z hD hqj
  have hciEq := coefficient_of_foc μ f Z hD hci (exp_pos _) hp hFqi hFi
  have hcjEq := coefficient_of_foc μ f Z hD hcj (exp_pos _) hp hFqj hFj
  have hpiEq := supplier_profit_of_equilibrium_foc μ f Z hD P i Cs Cr τ wi qi hci hFqi hwFi
  have hpjEq := supplier_profit_of_equilibrium_foc μ f Z hD P j Cs Cr τ wj qj hcj hFqj hwFj
  have hC : 0 < (P.c * exp (P.η Cs * P.t1)) / (exp (-(P.lamS * P.t1)) * P.p) :=
    div_pos (mul_pos hP.c_pos (exp_pos _)) (mul_pos (exp_pos _) hp)
  have hK : 0 < (1 - P.ρ Cs) * (P.c * exp (P.η Cs * P.t1)) :=
    mul_pos (rho_survival_pos μ f Z hD P hP hCs) (mul_pos hP.c_pos (exp_pos _))
  have hkStrict : StrictMonoOn (fun q => k μ q - q) {q | InSupport Z q} := by
    intro x hx y hy hxy
    exact k_sub_id_strict μ f Z hD hx hy hxy
  have hcle : coef P i Cs Cr τ ≤ coef P j Cs Cr τ ↔ qi ≤ qj := by
    rw [hciEq, hcjEq, mul_le_mul_iff_right₀ hC]
    exact (equilibrium_ratio_strict μ f Z hD).le_iff_le hqi hqj
  have hclt : coef P i Cs Cr τ < coef P j Cs Cr τ ↔ qi < qj := by
    rw [hciEq, hcjEq, mul_lt_mul_iff_right₀ hC]
    exact (equilibrium_ratio_strict μ f Z hD).lt_iff_lt hqi hqj
  have hple : supplierProfit P μ i Cs Cr τ wi qi ≤ supplierProfit P μ j Cs Cr τ wj qj ↔
      qi ≤ qj := by
    rw [hpiEq, hpjEq, mul_le_mul_iff_right₀ hK]
    exact hkStrict.le_iff_le hqi hqj
  have hplt : supplierProfit P μ i Cs Cr τ wi qi < supplierProfit P μ j Cs Cr τ wj qj ↔
      qi < qj := by
    rw [hpiEq, hpjEq, mul_lt_mul_iff_right₀ hK]
    exact hkStrict.lt_iff_lt hqi hqj
  exact ⟨hple.trans hcle.symm, hplt.trans hclt.symm⟩
