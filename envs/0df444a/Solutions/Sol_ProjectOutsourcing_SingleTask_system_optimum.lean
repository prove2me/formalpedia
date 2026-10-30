-- Prove2me | solution 1 for ProjectOutsourcing.SingleTask.system_optimum
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:02:54.572196+00:00
-- url     : https://prove2.me/submissions/57b02497-0f67-4e96-ab67-afe9cbd8a233

import Mathlib
import Definitions.Def_ProjectOutsourcing_SingleTask_Setting

open ProjectOutsourcing.SingleTask MeasureTheory Set Filter Topology

namespace PO_SysOpt

lemma ae_nonneg (M : Model) (hM : M.Valid) : ∀ᵐ z ∂M.μ, 0 ≤ z := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
  rw [this]; exact hM.nonneg

lemma ae_pos (M : Model) (hM : M.Valid) : ∀ᵐ z ∂M.μ, 0 < z := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iio 0 ∪ {0} := by
    ext a; simp [not_lt, le_iff_lt_or_eq]
  rw [this]
  refine measure_union_null hM.nonneg (hM.hasPdf Real.volume_singleton)

lemma F_nonneg (M : Model) (x : ℝ) : 0 ≤ M.F x := ENNReal.toReal_nonneg

lemma F_le_one (M : Model) (hM : M.Valid) (x : ℝ) : M.F x ≤ 1 := by
  have := hM.isProb
  unfold Model.F
  exact measureReal_le_one

lemma F_mono (M : Model) (hM : M.Valid) : Monotone M.F := by
  have := hM.isProb
  intro x y hxy
  unfold Model.F
  exact measureReal_mono (Iic_subset_Iic.mpr hxy)

lemma F_nonpos (M : Model) (hM : M.Valid) (x : ℝ) (hx : x ≤ 0) : M.F x = 0 := by
  have := hM.isProb
  unfold Model.F
  have h0 : M.μ (Iic x) = 0 := by
    have : Iic x ⊆ Iio 0 ∪ {0} := by
      intro a ha; simp only [mem_Iic] at ha
      rcases lt_or_eq_of_le (ha.trans hx) with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact measure_mono_null this (measure_union_null hM.nonneg (hM.hasPdf Real.volume_singleton))
  rw [h0]; rfl

lemma disc_le_one (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 ≤ s) : disc M s r ≤ 1 := by
  have := hM.isProb
  unfold disc
  split_ifs with hr
  · calc ∫ z, Real.exp (-(s * z / r)) ∂M.μ ≤ ∫ _z, (1:ℝ) ∂M.μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => (Real.exp_pos _).le)
            (integrable_const 1) ?_
          filter_upwards [ae_nonneg M hM] with z hz
          rw [Real.exp_le_one_iff]
          have : 0 ≤ s * z / r := div_nonneg (mul_nonneg hs hz) hr.le
          linarith
      _ = 1 := by simp
  · norm_num

lemma disc_nonneg (M : Model) (s r : ℝ) : 0 ≤ disc M s r := by
  unfold disc
  split_ifs
  · exact integral_nonneg fun _ => (Real.exp_pos _).le
  · exact le_rfl

lemma disc_repr_pos (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    disc M s r = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := by
  have := hM.isProb
  -- the kernel
  set f : ℝ → ℝ → ℝ := fun z t => (Ioi (z / r)).indicator (fun t => s * Real.exp (-(s * t))) t
    with hf
  -- z-side: f z t = (Iio (r t)).indicator const
  have hzt : ∀ z t, f z t = (Iio (r * t)).indicator (fun _ => s * Real.exp (-(s * t))) z := by
    intro z t
    simp only [hf, Set.indicator, Set.mem_Ioi, Set.mem_Iio]
    have : z / r < t ↔ z < r * t := by
      rw [div_lt_iff₀ hr, mul_comm]
    simp [this]
  -- singletons are null
  have hsing : ∀ a : ℝ, M.μ {a} = 0 := fun a => hM.hasPdf (Real.volume_singleton)
  have hinner_z : ∀ t, ∫ z, f z t ∂M.μ = s * Real.exp (-(s * t)) * M.F (r * t) := by
    intro t
    simp_rw [hzt]
    rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_comm]
    congr 1
    unfold Model.F
    rw [Measure.real, measure_congr (Iio_ae_eq_Iic' (hsing (r * t)))]
  -- t-side for z ≥ 0
  have hinner_t : ∀ z, 0 ≤ z → ∫ t in Ioi 0, f z t = Real.exp (-(s * z / r)) := by
    intro z hz
    simp only [hf]
    rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr (div_nonneg hz hr.le)]
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -s) (by linarith) (z / r)
    simp only [neg_mul] at this ⊢
    rw [this]
    field_simp
  -- a.e. nonnegativity
  have hae : ∀ᵐ z ∂M.μ, 0 ≤ z := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 ≤ a} = Iio 0 := by ext; simp
    rw [this]; exact hM.nonneg
  -- integrability on the product
  have hmeas : Measurable (Function.uncurry f) := by
    have : Function.uncurry f = fun p : ℝ × ℝ =>
        if p.1 / r < p.2 then s * Real.exp (-(s * p.2)) else 0 := by
      ext p; simp only [hf, Set.indicator, Function.uncurry, Set.mem_Ioi]
    rw [this]
    refine Measurable.ite ?_ (by fun_prop) measurable_const
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hint : Integrable (Function.uncurry f) (M.μ.prod (volume.restrict (Ioi (0:ℝ)))) := by
    have hg : Integrable (fun t : ℝ => s * Real.exp (-(s * t))) (volume.restrict (Ioi (0:ℝ))) := by
      have := (exp_neg_integrableOn_Ioi 0 hs).const_mul s
      simpa [neg_mul] using this
    have hb := (integrable_const (1:ℝ) (μ := M.μ)).mul_prod hg
    refine hb.mono' hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [Function.uncurry, hf, one_mul, Set.indicator]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp; positivity
  unfold disc
  rw [if_pos hr]
  calc ∫ z, Real.exp (-(s * z / r)) ∂M.μ = ∫ z, (∫ t in Ioi 0, f z t) ∂M.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with z hz
        exact (hinner_t z hz).symm
    _ = ∫ t in Ioi 0, ∫ z, f z t ∂M.μ := integral_integral_swap hint
    _ = ∫ t in Ioi 0, s * (Real.exp (-(s * t)) * M.F (r * t)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hinner_z, mul_assoc]
    _ = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := integral_const_mul _ _

lemma disc_repr (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 < s) :
    disc M s r = s * ∫ t in Set.Ioi 0, Real.exp (-(s * t)) * M.F (r * t) := by
  rcases lt_or_ge 0 r with hr | hr
  · exact disc_repr_pos M hM s r hs hr
  · have : disc M s r = 0 := by unfold disc; rw [if_neg (not_lt.mpr hr)]
    rw [this]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ)) (fun t ht => by
      simp only
      rw [F_nonpos M hM _ (mul_nonpos_of_nonpos_of_nonneg hr (le_of_lt ht)), mul_zero])]
    simp

lemma integrableOn_kernel (M : Model) (hM : M.Valid) (s r : ℝ) (hs : 0 < s) (hr : 0 ≤ r) :
    IntegrableOn (fun t => Real.exp (-(s * t)) * M.F (r * t)) (Ioi 0) := by
  have he : IntegrableOn (fun t : ℝ => Real.exp (-(s * t))) (Ioi 0) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi 0 hs
  refine he.mono' ?_ ?_
  · refine (Measurable.mul (by fun_prop) ?_).aestronglyMeasurable
    exact (F_mono M hM).measurable.comp (measurable_const_mul r)
  · refine Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (F_nonneg M _))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (F_le_one M hM _)

lemma disc_concave (M : Model) (hM : M.Valid) (s : ℝ) (hs : 0 < s) :
    ConcaveOn ℝ (Ici 0) (disc M s) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [disc_repr M hM s x hs, disc_repr M hM s y hs, disc_repr M hM s _ hs]
  have hix := integrableOn_kernel M hM s x hs hx
  have hiy := integrableOn_kernel M hM s y hs hy
  have hxy : 0 ≤ a * x + b * y := by
    have := mem_Ici.mp hx; have := mem_Ici.mp hy; positivity
  rw [← mul_assoc, ← mul_assoc, mul_comm a s, mul_comm b s, mul_assoc, mul_assoc, ← mul_add,
    ← integral_const_mul, ← integral_const_mul, ← integral_add (hix.const_mul a) (hiy.const_mul b)]
  refine mul_le_mul_of_nonneg_left ?_ hs.le
  refine setIntegral_mono_on ((hix.const_mul a).add (hiy.const_mul b))
    (integrableOn_kernel M hM s _ hs hxy) measurableSet_Ioi ?_
  intro t ht
  have ht' : (0:ℝ) ≤ t := le_of_lt ht
  have hc := hM.assumption1.concaveOn.2 (x := x * t) (y := y * t)
    (mem_Ici.mpr (mul_nonneg (mem_Ici.mp hx) ht')) (mem_Ici.mpr (mul_nonneg (mem_Ici.mp hy) ht'))
    ha hb hab
  simp only [smul_eq_mul] at hc
  have : (a * x + b * y) * t = a * (x * t) + b * (y * t) := by ring
  rw [this]
  have he := (Real.exp_pos (-(s * t))).le
  nlinarith [mul_le_mul_of_nonneg_left hc he]

lemma hasDerivAt_disc (M : Model) (hM : M.Valid) (s r₀ : ℝ) (hs : 0 ≤ s) (hr₀ : 0 < r₀) :
    HasDerivAt (disc M s) (s / r₀ ^ 2 * discZ M s r₀) r₀ := by
  have hprob := hM.isProb
  set F : ℝ → ℝ → ℝ := fun ρ z => Real.exp (-(s * z / ρ)) with hF
  set F' : ℝ → ℝ → ℝ := fun ρ z => Real.exp (-(s * z / ρ)) * (s * z / ρ ^ 2) with hF'
  have hball : Metric.ball r₀ (r₀ / 2) ∈ 𝓝 r₀ := Metric.ball_mem_nhds _ (by linarith)
  have hpos : ∀ ρ ∈ Metric.ball r₀ (r₀ / 2), r₀ / 2 < ρ := by
    intro ρ hρ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hρ
    linarith [hρ.1]
  have hmeas : ∀ ρ, AEStronglyMeasurable (F ρ) M.μ := fun ρ =>
    (by fun_prop : Continuous (F ρ)).aestronglyMeasurable
  have hint0 : Integrable (F r₀) M.μ := by
    refine (integrable_const (1:ℝ)).mono' (hmeas r₀) ?_
    filter_upwards [ae_nonneg M hM] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have : 0 ≤ s * z / r₀ := div_nonneg (mul_nonneg hs hz) hr₀.le
    linarith
  have hbound_int : Integrable (fun z => 4 * s / r₀ ^ 2 * ‖z‖) M.μ :=
    hM.integrable_id.norm.const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := M.μ) (F := F) (F' := F')
    (x₀ := r₀) (bound := fun z => 4 * s / r₀ ^ 2 * ‖z‖) hball
    (Eventually.of_forall hmeas) hint0
    ((by fun_prop : Continuous (F' r₀)).aestronglyMeasurable) ?_ hbound_int ?_
  · have heq : disc M s =ᶠ[𝓝 r₀] fun ρ => ∫ z, F ρ z ∂M.μ := by
      filter_upwards [Ioi_mem_nhds hr₀] with ρ hρ
      simp only [disc, if_pos (show (0:ℝ) < ρ from hρ), hF]
    have hval : ∫ z, F' r₀ z ∂M.μ = s / r₀ ^ 2 * discZ M s r₀ := by
      simp only [discZ, if_pos hr₀, hF']
      rw [← integral_const_mul]
      congr 1; ext z; ring
    rw [← hval]
    exact key.2.congr_of_eventuallyEq heq
  · filter_upwards [ae_nonneg M hM] with z hz
    intro ρ hρ
    have hρ2 := hpos ρ hρ
    have hρp : 0 < ρ := by linarith
    simp only [hF']
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, abs_of_nonneg hz]
    have h1 : Real.exp (-(s * z / ρ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ s * z / ρ := div_nonneg (mul_nonneg hs hz) hρp.le
      linarith
    have h2 : s * z / ρ ^ 2 ≤ 4 * s / r₀ ^ 2 * z := by
      rw [div_le_iff₀ (by positivity)]
      have : r₀ ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
      have hsz : 0 ≤ s * z := mul_nonneg hs hz
      calc s * z = s * z / r₀ ^ 2 * r₀ ^ 2 := by field_simp
        _ ≤ s * z / r₀ ^ 2 * (4 * ρ ^ 2) := by gcongr
        _ = 4 * s / r₀ ^ 2 * z * ρ ^ 2 := by ring
    calc Real.exp (-(s * z / ρ)) * (s * z / ρ ^ 2) ≤ 1 * (s * z / ρ ^ 2) := by
          gcongr
      _ ≤ 4 * s / r₀ ^ 2 * z := by linarith
  · refine Eventually.of_forall fun z ρ hρ => ?_
    have hρp : ρ ≠ 0 := by linarith [hpos ρ hρ]
    simp only [hF, hF']
    have h1 : HasDerivAt (fun ρ => -(s * z / ρ)) (s * z / ρ ^ 2) ρ := by
      have := (hasDerivAt_inv hρp).const_mul (-(s * z))
      have e1 : (fun ρ => -(s * z / ρ)) = fun y => -(s * z) * y⁻¹ := by ext x; ring
      have e2 : s * z / ρ ^ 2 = -(s * z) * -(ρ ^ 2)⁻¹ := by ring
      rw [e1, e2]; exact this
    exact h1.exp

lemma disc_tendsto_zero (M : Model) (hM : M.Valid) (s : ℝ) (hs : 0 < s) :
    Tendsto (disc M s) (𝓝[≥] 0) (𝓝 0) := by
  have hprob := hM.isProb
  set G : ℝ → ℝ → ℝ := fun r z => if 0 < r then Real.exp (-(s * z / r)) else 0 with hG
  have heq : disc M s = fun r => ∫ z, G r z ∂M.μ := by
    ext r; simp only [disc, hG]; split_ifs <;> simp
  rw [heq]
  have h0 : ∫ _z, (0:ℝ) ∂M.μ = 0 := by simp
  suffices Tendsto (fun r => ∫ z, G r z ∂M.μ) (𝓝[≥] 0) (𝓝 (∫ _z, (0:ℝ) ∂M.μ)) by
    rwa [h0] at this
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ)) ?_ ?_
    (integrable_const 1) ?_
  · refine Eventually.of_forall fun r => ?_
    simp only [hG]
    split_ifs
    · exact (by fun_prop : Continuous fun z => Real.exp (-(s * z / r))).aestronglyMeasurable
    · exact aestronglyMeasurable_const
  · refine Eventually.of_forall fun r => ?_
    filter_upwards [ae_nonneg M hM] with z hz
    simp only [hG]
    split_ifs with hr
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      have : 0 ≤ s * z / r := div_nonneg (mul_nonneg hs.le hz) hr.le
      linarith
    · simp
  · filter_upwards [ae_pos M hM] with z hz
    -- 0 ≤ G r z ≤ r / (s z)
    have hup : ∀ r, 0 ≤ r → G r z ≤ r / (s * z) := by
      intro r hr
      simp only [hG]
      split_ifs with hr'
      · have hx : 0 < s * z / r := by positivity
        have hx' : s * z / r ≤ Real.exp (s * z / r) := by
          linarith [Real.add_one_le_exp (s * z / r)]
        calc Real.exp (-(s * z / r)) = (Real.exp (s * z / r))⁻¹ := Real.exp_neg _
          _ ≤ (s * z / r)⁻¹ := inv_anti₀ hx hx'
          _ = r / (s * z) := inv_div _ _
      · positivity
    have hlo : ∀ r, 0 ≤ G r z := by
      intro r; simp only [hG]; split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
    have hlim : Tendsto (fun r : ℝ => r / (s * z)) (𝓝[≥] 0) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => r / (s * z)) (𝓝 0) (𝓝 (0 / (s * z))) :=
        (continuous_id.div_const _).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall hlo) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hup r hr

end PO_SysOpt

open PO_SysOpt in
theorem solution (M : Model) (hM : M.Valid) :
    ConcaveOn ℝ (Set.Ici 0) (sysProfit M) ∧ (∃! r, IsSystemOpt M r) ∧
      ∀ r, IsSystemOpt M r →
        HasDerivAt (sysProfit M)
            (M.Q * (M.alpha / r ^ 2) * discZ M M.alpha r - deriv M.c r) r ∧
          M.Q * (M.alpha / r ^ 2) * discZ M M.alpha r - deriv M.c r = 0 := by
  have hprob := hM.isProb
  have hα := hM.alpha_pos
  have hQ := hM.Q_pos
  -- cost facts
  have hc_cont : ContinuousOn M.c (Ici 0) := hM.c_diff.continuousOn
  have hc_nonneg : ∀ r, 0 ≤ r → 0 ≤ M.c r := fun r hr => by
    have := hM.c_mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hr) hr
    rwa [hM.c_zero] at this
  have hc1 : 0 < M.c 1 := by
    rcases (hc_nonneg 1 zero_le_one).lt_or_eq with h | h
    · exact h
    · exfalso
      have hs := hM.c_strictConvex.2 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
        (show (1:ℝ) ∈ Ici 0 from mem_Ici.mpr zero_le_one) (by norm_num)
        (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
      simp only [smul_eq_mul, hM.c_zero, ← h] at hs
      have := hc_nonneg (1/2 * 0 + 1/2 * 1) (by norm_num)
      linarith
  have hc_lin : ∀ r, 1 ≤ r → r * M.c 1 ≤ M.c r := by
    intro r hr
    have hr0 : 0 < r := by linarith
    have hcv := hM.c_strictConvex.convexOn.2 (show r ∈ Ici 0 from mem_Ici.mpr hr0.le)
      (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) (show (0:ℝ) ≤ 1/r by positivity)
      (show (0:ℝ) ≤ 1 - 1/r by rw [sub_nonneg, div_le_one hr0]; exact hr) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, hM.c_zero] at hcv
    rw [one_div_mul_cancel hr0.ne'] at hcv
    have := mul_le_mul_of_nonneg_left hcv hr0.le
    rw [← mul_assoc, mul_one_div_cancel hr0.ne', one_mul] at this
    exact this
  -- system profit facts
  have hP : ∀ r, sysProfit M r = M.Q * disc M M.alpha r - M.c r := fun r => rfl
  have hP0 : sysProfit M 0 = 0 := by
    rw [hP, hM.c_zero]; simp [disc]
  have hdc := disc_concave M hM M.alpha hα
  have hstrict : StrictConcaveOn ℝ (Ici 0) (sysProfit M) := by
    have h := (hdc.smul hQ.le).sub_strictConvexOn hM.c_strictConvex
    have e : sysProfit M = (fun r => M.Q • disc M M.alpha r) - M.c := by
      ext r; simp [hP, smul_eq_mul]
    rw [e]; exact h
  have hconc : ConcaveOn ℝ (Ici 0) (sysProfit M) := hstrict.concaveOn
  have hcont : ContinuousOn (sysProfit M) (Ici 0) := by
    intro x hx
    have hdisc : ContinuousWithinAt (disc M M.alpha) (Ici 0) x := by
      rcases (mem_Ici.mp hx).lt_or_eq with h | h
      · exact (hasDerivAt_disc M hM M.alpha x hα.le h).continuousAt.continuousWithinAt
      · subst h
        have h0 : disc M M.alpha 0 = 0 := by simp [disc]
        unfold ContinuousWithinAt
        rw [h0]
        exact disc_tendsto_zero M hM M.alpha hα
    exact (hdisc.const_mul M.Q).sub (hc_cont x hx)
  -- a point with positive system profit
  have hd1 : 0 < disc M M.alpha 1 := by
    unfold disc
    rw [if_pos zero_lt_one]
    refine integral_exp_pos ?_
    refine (integrable_const (1:ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_nonneg M hM] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have : 0 ≤ M.alpha * z / 1 := div_nonneg (mul_nonneg hα.le hz) zero_le_one
    linarith
  have hdlow : ∀ r, 0 ≤ r → r ≤ 1 → r * disc M M.alpha 1 ≤ disc M M.alpha r := by
    intro r hr0 hr1
    have := hdc.2 (show (1:ℝ) ∈ Ici 0 from mem_Ici.mpr zero_le_one)
      (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hr0 (show (0:ℝ) ≤ 1 - r by linarith) (by ring)
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at this
    have h0 : disc M M.alpha 0 = 0 := by simp [disc]
    rw [h0, mul_zero, add_zero] at this
    exact this
  obtain ⟨r₁, hr₁, hPr1⟩ : ∃ r₁, 0 < r₁ ∧ 0 < sysProfit M r₁ := by
    have hlo := hM.c_deriv_zero.isLittleO
    set ε := M.Q * disc M M.alpha 1 / 2 with hε
    have hεpos : 0 < ε := by positivity
    have hev := hlo.def hεpos
    have hev' : ∀ᶠ x in 𝓝[>] (0:ℝ), ‖M.c x - M.c 0 - (x - 0) • (0:ℝ)‖ ≤ ε * ‖x - 0‖ :=
      nhdsWithin_mono _ Ioi_subset_Ici_self hev
    obtain ⟨x, hx1, hx2⟩ := (hev'.and (Ioc_mem_nhdsGT (zero_lt_one' ℝ))).exists
    refine ⟨x, hx2.1, ?_⟩
    simp only [hM.c_zero, sub_zero, smul_zero, Real.norm_eq_abs] at hx1
    rw [abs_of_nonneg (hc_nonneg x hx2.1.le), abs_of_pos hx2.1] at hx1
    rw [hP]
    have := hdlow x hx2.1.le hx2.2
    have h2 : M.Q * (x * disc M M.alpha 1) ≤ M.Q * disc M M.alpha x :=
      mul_le_mul_of_nonneg_left this hQ.le
    have : 0 < M.Q * (x * disc M M.alpha 1) - ε * x := by
      rw [hε]; have := hx2.1; nlinarith [mul_pos hQ hd1]
    linarith
  -- every system-optimal rate is positive
  have hopt_pos : ∀ r, IsSystemOpt M r → 0 < r := by
    intro r ⟨hr0, hmax⟩
    rcases hr0.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hmax (mem_Ici.mpr hr₁.le)
      simp only [mem_ofPred_eq] at this
      rw [← h, hP0] at this
      linarith
  -- existence
  have hexists : ∃ r, IsSystemOpt M r := by
    set R := max 1 ((M.Q + 1) / M.c 1) with hR
    have hR1 : 1 ≤ R := le_max_left _ _
    obtain ⟨m, hm, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := R)).exists_isMaxOn
      (nonempty_Icc.2 (by linarith)) (hcont.mono Icc_subset_Ici_self)
    refine ⟨m, hm.1, ?_⟩
    intro r hr
    simp only [mem_ofPred_eq]
    by_cases hrR : r ≤ R
    · exact hmax ⟨hr, hrR⟩
    · push Not at hrR
      have h0m : sysProfit M 0 ≤ sysProfit M m := hmax ⟨le_rfl, by linarith⟩
      rw [hP0] at h0m
      have hdl := disc_le_one M hM M.alpha r hα.le
      have hcr := hc_lin r (by linarith)
      have hRr : (M.Q + 1) / M.c 1 * M.c 1 ≤ r * M.c 1 :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hrR.le) hc1.le
      rw [div_mul_cancel₀ _ hc1.ne'] at hRr
      rw [hP]
      nlinarith
  refine ⟨hconc, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hexists
    refine ⟨m, hm, fun y hy => ?_⟩
    by_contra hne
    have hs := hstrict.2 (show y ∈ Ici 0 from mem_Ici.mpr hy.1) (show m ∈ Ici 0 from mem_Ici.mpr hm.1)
      hne (show (0:ℝ) < 1/2 by norm_num) (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
    have h1 := hm.2 (mem_Ici.mpr hy.1)
    have h2 := hm.2 (show (1/2 : ℝ) • y + (1/2 : ℝ) • m ∈ Ici 0 by
      simp only [smul_eq_mul, mem_Ici]; have := hy.1; have := hm.1; positivity)
    have h3 := hy.2 (mem_Ici.mpr hm.1)
    simp only [mem_ofPred_eq, smul_eq_mul] at h1 h2 h3 hs
    linarith
  · intro r hr
    have hrpos := hopt_pos r hr
    have hd := hasDerivAt_disc M hM M.alpha r hα.le hrpos
    have hcd : HasDerivAt M.c (deriv M.c r) r :=
      ((hM.c_diff r (mem_Ici.mpr hrpos.le)).differentiableAt (Ici_mem_nhds hrpos)).hasDerivAt
    have hD : HasDerivAt (sysProfit M)
        (M.Q * (M.alpha / r ^ 2) * discZ M M.alpha r - deriv M.c r) r := by
      have := (hd.const_mul M.Q).sub hcd
      rw [mul_assoc]
      exact this
    refine ⟨hD, ?_⟩
    exact (hr.2.isLocalMax (Ici_mem_nhds hrpos)).hasDerivAt_eq_zero hD
