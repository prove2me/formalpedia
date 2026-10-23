-- Prove2me | solution 1 for VerticalOwnership.CheapTalk.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T15:18:38.219367+00:00
-- url     : https://prove2.me/submissions/c9ff084e-a2f5-471a-bfdd-dfb5f7e06392

import Mathlib
import Definitions.Def_VerticalOwnership_CheapTalk_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace VOCTAux

open VerticalOwnership.CheapTalk Set

/-- The cdf of an absolutely continuous probability measure is continuous. -/
lemma cdf_continuous (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P ≪ volume) :
    Continuous (cdf P) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hsing : (cdf P).measure {x} = 0 := by
    rw [measure_cdf]; exact hP Real.volume_singleton
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hll : Function.leftLim (cdf P) x ≤ cdf P x := (cdf P).mono.leftLim_le le_rfl
  have heq : Function.leftLim (cdf P) x = cdf P x := le_antisymm hll (by linarith)
  have hleft : ContinuousWithinAt (cdf P) (Iio x) x :=
    ((cdf P).mono.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  have hright : ContinuousWithinAt (cdf P) (Ici x) x := (cdf P).right_continuous x
  rw [continuousWithinAt_Iio_iff_Iic] at hleft
  exact continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩

/-- The quantile of a continuous cdf hits the level exactly. -/
lemma quantile_spec (F : ℝ → ℝ) (hFc : Continuous F)
    (hbot : Tendsto F atBot (𝓝 0)) (htop : Tendsto F atTop (𝓝 1)) (z : ℝ) (hz0 : 0 < z)
    (hz1 : z < 1) : F (sInf {x | z ≤ F x}) = z := by
  set S := {x | z ≤ F x} with hSdef
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := (htop.eventually (lt_mem_nhds hz1)).exists
    exact ⟨x, hx.le⟩
  have hbdd : BddBelow S := by
    obtain ⟨x0, hx0⟩ := eventually_atBot.1 (hbot.eventually (gt_mem_nhds hz0))
    refine ⟨x0, fun x hx => ?_⟩
    by_contra h
    push_neg at h
    have := hx0 x h.le
    simp only [hSdef, mem_setOf_eq] at hx
    linarith
  have hcl : IsClosed S := isClosed_le continuous_const hFc
  have hmem : sInf S ∈ S := hcl.csInf_mem hne hbdd
  refine le_antisymm ?_ hmem
  by_contra h
  push_neg at h
  have hev : ∀ᶠ x in 𝓝 (sInf S), z < F x := (hFc.tendsto _).eventually (lt_mem_nhds h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hx : z < F (sInf S - ε / 2) := hball (by
    rw [Real.dist_eq, show sInf S - ε / 2 - sInf S = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]
    linarith)
  have : sInf S ≤ sInf S - ε / 2 := csInf_le hbdd hx.le
  linarith

/-- `E[min ε t₂ − min ε t₁] = ∫_{t₁}^{t₂} (1 − F)`. -/
lemma integral_min_sub (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P ≪ volume)
    (t1 t2 : ℝ) (h : t1 ≤ t2) :
    ∫ e, (min e t2 - min e t1) ∂P = ∫ x in t1..t2, (1 - cdf P x) := by
  set ν : Measure ℝ := volume.restrict (Ioc t1 t2) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set S : Set (ℝ × ℝ) := {p | p.2 ≤ p.1} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_fst
  set f : ℝ → ℝ → ℝ := fun e x => S.indicator (fun _ => (1 : ℝ)) (e, x) with hfdef
  have hf : Integrable (Function.uncurry f) (P.prod ν) := by
    have : Function.uncurry f = S.indicator (fun _ => (1 : ℝ)) := by
      funext p; rfl
    rw [this]
    exact (integrable_const (1 : ℝ)).indicator hS
  have hswap := integral_integral_swap hf
  have h1 : ∀ e, ∫ x, f e x ∂ν = min e t2 - min e t1 := by
    intro e
    have : (fun x => f e x) = (Iic e).indicator (1 : ℝ → ℝ) := by
      ext x; simp [hfdef, hSdef, Set.indicator]
    rw [this, integral_indicator_one measurableSet_Iic]
    rw [Measure.real, hν, Measure.restrict_apply measurableSet_Iic, Set.inter_comm,
      Set.Ioc_inter_Iic, Real.volume_Ioc, ENNReal.toReal_ofReal']
    rcases le_total e t1 with h' | h'
    · rw [min_eq_left (le_trans h' h), min_eq_left h', min_eq_right (le_trans h' h)]
      simp; linarith
    · rcases le_total e t2 with h'' | h''
      · rw [min_eq_left h'', min_eq_right h', min_eq_right h'']
        rw [max_eq_left (by linarith)]
      · rw [min_eq_right h'', min_eq_right h', min_eq_left h'']
        rw [max_eq_left (by linarith)]
  have h2 : ∀ x, ∫ e, f e x ∂P = 1 - cdf P x := by
    intro x
    have : (fun e => f e x) = (Ici x).indicator (1 : ℝ → ℝ) := by
      ext e; simp [hfdef, hSdef, Set.indicator]
    rw [this, integral_indicator_one measurableSet_Ici]
    have hx0 : P {x} = 0 := hP Real.volume_singleton
    rw [Measure.real, ← measure_congr (Ioi_ae_eq_Ici' hx0), ← compl_Iic,
      prob_compl_eq_one_sub measurableSet_Iic, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      cdf_eq_real, Measure.real]
    simp
  calc ∫ e, (min e t2 - min e t1) ∂P = ∫ e, ∫ x, f e x ∂ν ∂P := by
        congr 1; ext e; rw [h1 e]
    _ = ∫ x, ∫ e, f e x ∂P ∂ν := hswap
    _ = ∫ x in Ioc t1 t2, (1 - cdf P x) := by
        rw [hν]; congr 1; ext x; rw [h2 x]
    _ = ∫ x in t1..t2, (1 - cdf P x) := (intervalIntegral.integral_of_le h).symm

lemma hint (P : Measure ℝ) [IsProbabilityMeasure P] (hi : Integrable id P) (μ K : ℝ) :
    Integrable (fun e => min (μ + e) K) P := by
  have h1 : Integrable (fun e : ℝ => μ + e) P := (integrable_const μ).add hi
  have := h1.inf (integrable_const K)
  refine this.congr (Eventually.of_forall fun e => ?_)
  rfl

lemma E_diff (P : Measure ℝ) [IsProbabilityMeasure P] (hP : P ≪ volume) (hi : Integrable id P)
    (μ K1 K2 : ℝ) (h : K1 ≤ K2) :
    ∫ e, min (μ + e) K2 ∂P - ∫ e, min (μ + e) K1 ∂P
      = ∫ x in (K1 - μ)..(K2 - μ), (1 - cdf P x) := by
  rw [← integral_sub (hint P hi μ K2) (hint P hi μ K1),
    ← integral_min_sub P hP _ _ (by linarith)]
  congr 1; ext e
  simp only [min_def]
  split_ifs <;> linarith

lemma ae_gt_lo (M : Model) (hM : M.Standing) : ∀ᵐ e ∂M.P, M.εlo < e := by
  haveI := hM.prob
  have h := hM.cdf_εlo
  rw [cdf_eq_real] at h
  have h0 : M.P (Iic M.εlo) = 0 := (measureReal_eq_zero_iff).1 h
  rw [ae_iff]
  have : {a : ℝ | ¬ M.εlo < a} = Iic M.εlo := by ext; simp
  rw [this]; exact h0

lemma πs_eq (M : Model) (hM : M.Standing) (μ K : ℝ) (hμ : M.μL ≤ μ) :
    M.πs μ 0 K = M.w * ∫ e, min (μ + e) K ∂M.P - M.c * K := by
  haveI := hM.prob
  have hae := ae_gt_lo M hM
  have hi := hint M.P hM.integrable μ K
  unfold Model.πs
  rw [integral_congr_ae (g := fun e => M.w * min (μ + e) K - M.c * K)]
  · rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp
  · filter_upwards [hae] with e he
    have : 0 ≤ μ + e := by linarith [hM.demand_nonneg]
    simp only [max_eq_left this, min_comm K]

lemma πr_eq (M : Model) (hM : M.Standing) (μ K : ℝ) (hμ : M.μL ≤ μ) :
    M.πr μ 0 K = (M.r - M.w) * ∫ e, min (μ + e) K ∂M.P := by
  haveI := hM.prob
  have hae := ae_gt_lo M hM
  unfold Model.πr
  rw [integral_congr_ae (g := fun e => (M.r - M.w) * min (μ + e) K), integral_const_mul]
  filter_upwards [hae] with e he
  have : max (0 - μ - e) 0 = 0 := max_eq_right (by linarith [hM.demand_nonneg])
  simp only [this, mul_zero, sub_zero]

section avg

variable (F : ℝ → ℝ) (a : ℝ)

lemma avg_lt (hFc : Continuous F) (hFm : Monotone F) (hstrict : ∀ x, a < x → F a < F x)
    (d : ℝ) (hd : 0 < d) : ∫ x in a..d + a, F x < d * F (d + a) := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := F) (g := fun _ => F (d + a)) (a := a) (b := d + a) (by linarith) hFc.continuousOn
    continuousOn_const (fun x hx => hFm hx.2) ⟨a, ⟨le_rfl, by linarith⟩, hstrict _ (by linarith)⟩
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_right] at h

lemma avg_gt (hFc : Continuous F) (hstrict : ∀ x, a < x → F a < F x)
    (d : ℝ) (hd : 0 < d) : d * F a < ∫ x in a..d + a, F x := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ => F a) (g := F) (a := a) (b := d + a) (by linarith) continuousOn_const
    hFc.continuousOn (fun x hx => (hstrict x hx.1).le)
    ⟨d + a, ⟨by linarith, le_rfl⟩, hstrict _ (by linarith)⟩
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_right] at h

lemma avg_lt_one (hFc : Continuous F) (hF1 : ∀ x, F x ≤ 1) (hFa : F a < 1)
    (d : ℝ) (hd : 0 < d) : ∫ x in a..d + a, F x < d := by
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := F) (g := fun _ => (1 : ℝ)) (a := a) (b := d + a) (by linarith) hFc.continuousOn
    continuousOn_const (fun x _ => hF1 x) ⟨a, ⟨le_rfl, by linarith⟩, hFa⟩
  rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_right, mul_one] at h

lemma avg_strictMono (hFc : Continuous F) (hFm : Monotone F)
    (hstrict : ∀ x, a < x → F a < F x) :
    StrictMonoOn (fun d => (1 / d) * ∫ x in a..d + a, F x) (Ioi 0) := by
  intro d1 hd1 d2 hd2 h12
  simp only [mem_Ioi] at hd1 hd2
  have hsplit : ∫ x in a..d2 + a, F x
      = (∫ x in a..d1 + a, F x) + ∫ x in (d1 + a)..(d2 + a), F x :=
    (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
      (hFc.intervalIntegrable _ _)).symm
  have hJ : (d2 - d1) * F (d1 + a) ≤ ∫ x in (d1 + a)..(d2 + a), F x := by
    have := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => F (d1 + a)) (g := F)
      (by linarith : d1 + a ≤ d2 + a) (continuous_const.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)
      (fun x hx => hFm hx.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc (d2 - d1) * F (d1 + a) = (d2 + a - (d1 + a)) * F (d1 + a) := by ring
      _ ≤ _ := this
  have hI1 := avg_lt F a hFc hFm hstrict d1 hd1
  show (1 / d1) * ∫ x in a..d1 + a, F x < (1 / d2) * ∫ x in a..d2 + a, F x
  rw [one_div_mul_eq_div, one_div_mul_eq_div, div_lt_div_iff₀ hd1 hd2, hsplit]
  nlinarith [mul_pos (sub_pos.2 h12) (sub_pos.2 hI1), mul_le_mul_of_nonneg_left hJ hd1.le]

lemma avg_continuousOn (hFc : Continuous F) :
    ContinuousOn (fun d => (1 / d) * ∫ x in a..d + a, F x) (Ioi 0) := by
  have hprim : Continuous (fun d => ∫ x in a..d + a, F x) :=
    (intervalIntegral.continuous_primitive (fun _ _ => hFc.intervalIntegrable _ _) a).comp
      (continuous_id.add continuous_const)
  refine ContinuousOn.mul ?_ hprim.continuousOn
  exact continuousOn_const.div continuousOn_id (fun x hx => (mem_Ioi.1 hx).ne')

lemma avg_exists (hFc : Continuous F) (hFm : Monotone F) (hF0 : ∀ x, 0 ≤ F x)
    (htop : Tendsto F atTop (𝓝 1)) (θ : ℝ) (hθ0 : F a < θ) (hθ1 : θ < 1) :
    ∃ d, 0 < d ∧ (1 / d) * ∫ x in a..d + a, F x = θ := by
  set g := fun d : ℝ => (1 / d) * ∫ x in a..d + a, F x with hg
  have hev : ∀ᶠ x in 𝓝 a, F x < θ := (hFc.tendsto a).eventually (gt_mem_nhds hθ0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set d1 := ε / 2 with hd1def
  have hd1 : 0 < d1 := half_pos hε
  have hFd1 : F (d1 + a) < θ := hball (by
    rw [Real.dist_eq, add_sub_cancel_right, abs_of_pos hd1]; linarith)
  have hg1 : g d1 ≤ θ := by
    have := intervalIntegral.integral_mono_on (μ := volume) (f := F) (g := fun _ => F (d1 + a))
      (by linarith : a ≤ d1 + a) (hFc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      (fun x hx => hFm hx.2)
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_right] at this
    simp only [hg]
    rw [one_div_mul_eq_div, div_le_iff₀ hd1]
    linarith [mul_lt_mul_of_pos_left hFd1 hd1]
  set m := (θ + 1) / 2 with hm
  have hθm : θ < m := by rw [hm]; linarith
  have hm1 : m < 1 := by rw [hm]; linarith
  have hθpos : 0 < θ := lt_of_le_of_lt (hF0 a) hθ0
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (htop.eventually (lt_mem_nhds hm1))
  set x1 := max x0 a with hx1
  have hx1a : 0 ≤ x1 - a := sub_nonneg.2 (le_max_right _ _)
  set k := (x1 - a) * m / (m - θ) with hkdef
  have hk : k * (m - θ) = (x1 - a) * m := div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 hθm))
  have hk0 : 0 ≤ k := div_nonneg (mul_nonneg hx1a (by linarith)) (by linarith)
  set d2 := k + (x1 - a) + d1 + 1 with hd2def
  have hd2 : d1 < d2 := by rw [hd2def]; linarith
  have hd2pos : 0 < d2 := by linarith
  have hg2 : θ ≤ g d2 := by
    have hsplit : ∫ x in a..d2 + a, F x = (∫ x in a..x1, F x) + ∫ x in x1..(d2 + a), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _)).symm
    have h1 : 0 ≤ ∫ x in a..x1, F x :=
      intervalIntegral.integral_nonneg (by linarith) (fun x _ => hF0 x)
    have hx1d2 : x1 ≤ d2 + a := by rw [hd2def]; linarith
    have h2 : (d2 + a - x1) * m ≤ ∫ x in x1..(d2 + a), F x := by
      have := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => m) (g := F) hx1d2
        (continuous_const.intervalIntegrable _ _) (hFc.intervalIntegrable _ _)
        (fun x hx => (hx0 x (le_trans (le_max_left _ _) hx.1)).le)
      rwa [intervalIntegral.integral_const, smul_eq_mul] at this
    have hid : (d2 + a - x1) * m - θ * d2
        = (x1 - a + d1 + 1) * (m - θ) + (k * (m - θ) - (x1 - a) * m) := by
      rw [hd2def]; ring
    have hpos : 0 ≤ (x1 - a + d1 + 1) * (m - θ) :=
      mul_nonneg (by linarith) (by linarith)
    simp only [hg]
    rw [one_div_mul_eq_div, le_div_iff₀ hd2pos, hsplit]
    linarith
  have hcont : ContinuousOn g (Icc d1 d2) :=
    (avg_continuousOn F a hFc).mono (fun x hx => lt_of_lt_of_le hd1 hx.1)
  obtain ⟨d, hd, hgd⟩ := intermediate_value_Icc hd2.le hcont ⟨hg1, hg2⟩
  exact ⟨d, lt_of_lt_of_le hd1 hd.1, hgd⟩

end avg

end VOCTAux

set_option maxHeartbeats 1000000 in
open VerticalOwnership.CheapTalk in
theorem solution (M : Model) (hM : M.Standing) :
    (∀ β ∈ Set.Icc (0 : ℝ) 1, M.cond12 β) ∧
    (∀ β ∈ Set.Icc (0 : ℝ) 1, (M.cond12 β ∧ M.cond13 β) ↔ M.betaCT ≤ β) ∧
    M.betaCT = M.zr / (1 - M.zr) * ((1 - M.zs) / (M.R M.Δ - M.zs) - 1) ∧
    M.R M.Δ < 1 ∧
    (∀ β ∈ Set.Ioc (0 : ℝ) 1, ∃! d : ℝ, 0 < d ∧ M.R d = M.theta β) ∧
    (∀ β ∈ Set.Ioc (0 : ℝ) 1, ∀ d : ℝ, 0 < d → M.R d = M.theta β →
      (M.cond12 β ∧ M.cond13 β) → d ≤ M.Δ) := by
  haveI := hM.prob
  have hFc : Continuous (cdf M.P) := VOCTAux.cdf_continuous M.P hM.density
  have hFm : Monotone (cdf M.P) := (cdf M.P).mono
  have hc := hM.c_pos
  have hcw := hM.c_lt_w
  have hwr := hM.w_lt_r
  have hw : 0 < M.w := by linarith
  have hr : 0 < M.r := by linarith
  have hzs : M.zs = 1 - M.c / M.w := rfl
  have h1zs : 1 - M.zs = M.c / M.w := by rw [hzs]; ring
  have hzs0 : 0 < M.zs := by rw [hzs, sub_pos, div_lt_one hw]; exact hcw
  have hzs1 : M.zs < 1 := by rw [hzs]; have := div_pos hc hw; linarith
  have hwzs : M.w * (1 - M.zs) = M.c := by rw [h1zs]; field_simp
  have hzr_eq : M.zr = (M.r - M.w) / M.r := by
    show 1 - M.w / M.r = _; field_simp
  -- the quantile a = F⁻¹(z_s)
  set a := M.Finv M.zs with ha_def
  have hFa : cdf M.P a = M.zs :=
    VOCTAux.quantile_spec (cdf M.P) hFc (tendsto_cdf_atBot M.P) (tendsto_cdf_atTop M.P)
      M.zs hzs0 hzs1
  have hlo : M.εlo < a := by
    by_contra h
    push_neg at h
    have := hFm h
    rw [hFa, hM.cdf_εlo] at this
    linarith
  have hgt : ∀ x, a < x → cdf M.P a < cdf M.P x := fun x hx =>
    hM.strictMono a x hlo.le hx (by rw [hFa]; exact hzs1)
  have hle : ∀ x, x ≤ a → cdf M.P x ≤ M.zs := fun x hx => hFa ▸ hFm hx
  have hΔ : 0 < M.Δ := by show 0 < M.μH - M.μL; linarith [hM.μL_lt_μH]
  have hμ : M.μL ≤ M.μH := hM.μL_lt_μH.le
  -- capacities
  have hKdiff : M.KH - M.KL = M.Δ := by
    show (M.μH + a) - (M.μL + a) = M.μH - M.μL; ring
  have hKLH : M.KL - M.μH = a - M.Δ := by
    show (M.μL + a) - M.μH = a - (M.μH - M.μL); ring
  have hKHH : M.KH - M.μH = a := by show (M.μH + a) - M.μH = a; ring
  have hKLL : M.KL - M.μL = a := by show (M.μL + a) - M.μL = a; ring
  have hKHL : M.KH - M.μL = M.Δ + a := by
    show (M.μH + a) - M.μL = (M.μH - M.μL) + a; ring
  have hKLKH : M.KL ≤ M.KH := by linarith
  -- the two expectation gaps
  set I := ∫ x in a..M.Δ + a, cdf M.P x with hIdef
  set DH := ∫ x in (a - M.Δ)..a, (1 - cdf M.P x) with hDHdef
  have hDH' : ∫ e, min (M.μH + e) M.KH ∂M.P - ∫ e, min (M.μH + e) M.KL ∂M.P = DH := by
    rw [VOCTAux.E_diff M.P hM.density hM.integrable _ _ _ hKLKH, hKLH, hKHH]
  have hDL' : ∫ e, min (M.μL + e) M.KH ∂M.P - ∫ e, min (M.μL + e) M.KL ∂M.P = M.Δ - I := by
    rw [VOCTAux.E_diff M.P hM.density hM.integrable _ _ _ hKLKH, hKLL, hKHL,
      intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (hFc.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul, mul_one, add_sub_cancel_right]
  have hDH : M.Δ * (1 - M.zs) ≤ DH := by
    have := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => 1 - M.zs)
      (g := fun x => 1 - cdf M.P x) (by linarith : a - M.Δ ≤ a) (continuous_const.intervalIntegrable _ _)
      ((continuous_const.sub hFc).intervalIntegrable _ _) (fun x hx => by linarith [hle x hx.2])
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    calc M.Δ * (1 - M.zs) = (a - (a - M.Δ)) * (1 - M.zs) := by ring
      _ ≤ _ := this
  have hIgt : M.Δ * M.zs < I := by
    have := VOCTAux.avg_gt (cdf M.P) a hFc hgt M.Δ hΔ
    rwa [hFa] at this
  have hIlt : I < M.Δ :=
    VOCTAux.avg_lt_one (cdf M.P) a hFc (fun x => cdf_le_one M.P x) (by rw [hFa]; exact hzs1) M.Δ hΔ
  set B := M.c * M.Δ - M.w * (M.Δ - I) with hBdef
  have hBeq : B = M.w * (I - M.Δ * M.zs) := by
    rw [hBdef, ← hwzs]; ring
  have hB : 0 < B := by rw [hBeq]; exact mul_pos hw (by linarith)
  -- payoffs
  have h12 : ∀ β : ℝ, M.vr β M.μH 0 M.KH - M.vr β M.μH 0 M.KL
      = (M.r - M.w + β * M.w) * DH - β * M.c * M.Δ := by
    intro β
    unfold Model.vr
    rw [VOCTAux.πr_eq M hM _ _ hμ, VOCTAux.πr_eq M hM _ _ hμ, VOCTAux.πs_eq M hM _ _ hμ,
      VOCTAux.πs_eq M hM _ _ hμ]
    linear_combination (M.r - M.w + β * M.w) * hDH' - β * M.c * hKdiff
  have h13 : ∀ β : ℝ, M.vr β M.μL 0 M.KL - M.vr β M.μL 0 M.KH
      = β * B - (M.r - M.w) * (M.Δ - I) := by
    intro β
    unfold Model.vr
    rw [VOCTAux.πr_eq M hM _ _ le_rfl, VOCTAux.πr_eq M hM _ _ le_rfl,
      VOCTAux.πs_eq M hM _ _ le_rfl, VOCTAux.πs_eq M hM _ _ le_rfl, hBdef]
    linear_combination (-(M.r - M.w + β * M.w)) * hDL' + β * M.c * hKdiff
  have hc12 : ∀ β ∈ Set.Icc (0 : ℝ) 1, M.cond12 β := by
    intro β hβ
    have hβ0 := hβ.1
    unfold Model.cond12
    have hcoef : 0 ≤ M.r - M.w + β * M.w := add_nonneg (by linarith) (mul_nonneg hβ0 hw.le)
    have k1 := mul_le_mul_of_nonneg_left hDH hcoef
    have k2 : 0 ≤ (M.r - M.w) * (M.Δ * (1 - M.zs)) :=
      mul_nonneg (by linarith) (mul_nonneg hΔ.le (by linarith))
    have k3 : β * M.Δ * (M.w * (1 - M.zs)) = β * M.Δ * M.c := by rw [hwzs]
    have := h12 β
    linarith
  have hc13 : ∀ β : ℝ, M.cond13 β ↔ (M.r - M.w) * (M.Δ - I) ≤ β * B := by
    intro β
    unfold Model.cond13
    have := h13 β
    constructor <;> intro h <;> linarith
  have hbeta : M.betaCT = (M.r - M.w) * (M.Δ - I) / B := by
    have hnum : M.πr M.μL 0 M.KH - M.πr M.μL 0 M.KL = (M.r - M.w) * (M.Δ - I) := by
      rw [VOCTAux.πr_eq M hM _ _ le_rfl, VOCTAux.πr_eq M hM _ _ le_rfl]
      linear_combination (M.r - M.w) * hDL'
    have hden : M.πs M.μL 0 M.KL - M.πs M.μL 0 M.KH = B := by
      rw [VOCTAux.πs_eq M hM _ _ le_rfl, VOCTAux.πs_eq M hM _ _ le_rfl, hBdef]
      linear_combination (-M.w) * hDL' + M.c * hKdiff
    show (M.πr M.μL 0 M.KH - M.πr M.μL 0 M.KL) / (M.πs M.μL 0 M.KL - M.πs M.μL 0 M.KH) = _
    rw [hnum, hden]
  have hRdef : ∀ d, M.R d = (1 / d) * ∫ x in a..d + a, cdf M.P x := fun d => rfl
  have hRΔ : M.R M.Δ = I / M.Δ := by rw [hRdef, one_div_mul_eq_div]
  have hRz : M.R M.Δ - M.zs = B / (M.w * M.Δ) := by
    rw [hRΔ, hBeq]; field_simp
  -- theta
  have hθ : ∀ β : ℝ, 0 < β →
      M.theta β = M.zs + M.c * (M.r - M.w) / (M.w * (M.r - M.w + β * M.w)) := by
    intro β hβ
    have hrw : 0 < M.r - M.w := by linarith
    have hden : 0 < M.r - M.w + β * M.w := add_pos_of_pos_of_nonneg hrw (mul_nonneg hβ.le hw.le)
    have hinv : 1 / M.zr - 1 = M.w / (M.r - M.w) := by
      rw [hzr_eq, one_div_div]; field_simp; ring
    show M.zs + (1 - M.zs) / (1 + β * (1 / M.zr - 1)) = _
    rw [hinv, h1zs]
    congr 1
    have h1 : 1 + β * (M.w / (M.r - M.w)) = (M.r - M.w + β * M.w) / (M.r - M.w) := by
      field_simp
    rw [h1]
    field_simp
  have hθbounds : ∀ β ∈ Set.Ioc (0 : ℝ) 1, M.zs < M.theta β ∧ M.theta β < 1 := by
    intro β hβ
    have hβ0 := hβ.1
    have hrw : 0 < M.r - M.w := by linarith
    have hden : 0 < M.w * (M.r - M.w + β * M.w) := mul_pos hw (add_pos_of_pos_of_nonneg hrw (mul_nonneg hβ0.le hw.le))
    rw [hθ β hβ0]
    constructor
    · have : 0 < M.c * (M.r - M.w) / (M.w * (M.r - M.w + β * M.w)) :=
        div_pos (mul_pos hc hrw) hden
      linarith
    · have : M.c * (M.r - M.w) / (M.w * (M.r - M.w + β * M.w)) < M.c / M.w := by
        rw [div_lt_div_iff₀ hden hw]
        linarith [mul_pos (mul_pos hc hw) (mul_pos hβ0 hw)]
      linarith
  have hmono := VOCTAux.avg_strictMono (cdf M.P) a hFc hFm hgt
  refine ⟨hc12, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    rw [hbeta, div_le_iff₀ hB, ← hc13]
    exact ⟨fun h => h.2, fun h => ⟨hc12 β hβ, h⟩⟩
  · rw [hbeta, hzr_eq, hRz]
    have hrw : 0 < M.r - M.w := by linarith
    have h1 : 1 - (M.r - M.w) / M.r = M.w / M.r := by field_simp; ring
    rw [h1, h1zs]
    field_simp
    ring
  · rw [hRΔ, div_lt_one hΔ]; exact hIlt
  · intro β hβ
    obtain ⟨hlo', hhi'⟩ := hθbounds β hβ
    obtain ⟨d, hd, hgd⟩ := VOCTAux.avg_exists (cdf M.P) a hFc hFm (fun x => cdf_nonneg M.P x)
      (tendsto_cdf_atTop M.P) (M.theta β) (by rw [hFa]; exact hlo') hhi'
    refine ⟨d, ⟨hd, by rw [hRdef]; exact hgd⟩, ?_⟩
    rintro d' ⟨hd', hgd'⟩
    by_contra hne
    rw [hRdef] at hgd'
    rcases lt_or_gt_of_ne hne with h | h
    · have := hmono hd' hd h
      simp only at this
      linarith
    · have := hmono hd hd' h
      simp only at this
      linarith
  · intro β hβ d hd hRd hcond
    have hβ0 := hβ.1
    have h13' := (hc13 β).1 hcond.2
    have hrw : 0 < M.r - M.w := by linarith
    have hden : 0 < M.w * (M.r - M.w + β * M.w) := mul_pos hw (add_pos_of_pos_of_nonneg hrw (mul_nonneg hβ0.le hw.le))
    have hθle : M.theta β ≤ M.R M.Δ := by
      rw [hθ β hβ0]
      have hR' : M.R M.Δ = M.zs + B / (M.w * M.Δ) := by rw [← hRz]; ring
      rw [hR']
      have : M.c * (M.r - M.w) / (M.w * (M.r - M.w + β * M.w)) ≤ B / (M.w * M.Δ) := by
        rw [div_le_div_iff₀ hden (mul_pos hw hΔ)]
        have := mul_le_mul_of_nonneg_left h13' (mul_nonneg hw.le hw.le)
        have hBw : M.w * (M.r - M.w) * B = M.w * (M.r - M.w) * (M.c * M.Δ - M.w * (M.Δ - I)) := by
          rw [hBdef]
        linarith
      linarith
    by_contra hlt
    push_neg at hlt
    have := hmono hΔ hd hlt
    simp only at this
    rw [hRdef] at hRd hθle
    linarith
