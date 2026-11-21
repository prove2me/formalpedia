-- Prove2me | solution 1 for PalmQueueing.Formulas.pollaczek_khinchin
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:06:57.321849+00:00
-- url     : https://prove2.me/submissions/04f348df-a861-4f7d-98a5-11f552ff54f4

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

namespace Aux_pk

open MeasureTheory Filter Topology
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Elementary facts about `t ↦ exp(i u t)` -/

noncomputable def gf (u : ℝ) (w : ℝ) : ℂ :=
  Set.indicator (Set.Ioi (0:ℝ)) (fun x : ℝ => Complex.exp (Complex.I * u * x)) w

lemma norm_cexp (u x : ℝ) : ‖Complex.exp (Complex.I * u * x)‖ = 1 := by
  rw [show Complex.I * (u:ℂ) * (x:ℂ) = ((u * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma measurable_cexp (u : ℝ) : Measurable (fun x : ℝ => Complex.exp (Complex.I * u * x)) :=
  Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)

lemma gf_meas (u : ℝ) : Measurable (gf u) :=
  (measurable_cexp u).indicator measurableSet_Ioi

lemma gf_norm (u w : ℝ) : ‖gf u w‖ ≤ 1 := by
  unfold gf
  by_cases h : w ∈ Set.Ioi (0:ℝ)
  · rw [Set.indicator_of_mem h, norm_cexp]
  · rw [Set.indicator_of_notMem h, norm_zero]; norm_num

/-- Fundamental theorem of calculus for `exp(i u (c - (s - T0))⁺)`. -/
lemma piece (u c T0 a b : ℝ) (hab : a ≤ b) :
    Complex.exp (Complex.I * u * ((max (c - (b - T0)) 0 : ℝ) : ℂ))
      - Complex.exp (Complex.I * u * ((max (c - (a - T0)) 0 : ℝ) : ℂ))
      = -(Complex.I * u) * ∫ s in a..b, gf u (max (c - (s - T0)) 0) := by
  have hL : Continuous (fun s : ℝ => c - (s - T0)) :=
    continuous_const.sub (continuous_id.sub continuous_const)
  have hH : Continuous (fun s : ℝ => max (c - (s - T0)) 0) := hL.max continuous_const
  have key : ∫ s in a..b, -(Complex.I * u) * gf u (max (c - (s - T0)) 0)
      = Complex.exp (Complex.I * u * ((max (c - (b - T0)) 0 : ℝ) : ℂ))
        - Complex.exp (Complex.I * u * ((max (c - (a - T0)) 0 : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun s : ℝ => Complex.exp (Complex.I * u * ((max (c - (s - T0)) 0 : ℝ) : ℂ)))
      (f' := fun s : ℝ => -(Complex.I * u) * gf u (max (c - (s - T0)) 0)) hab ?_ ?_ ?_
    · exact (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hH))).continuousOn
    · intro x _
      by_cases hx : 0 < c - (x - T0)
      · have hev : ∀ᶠ s in 𝓝 x, 0 < c - (s - T0) :=
          Filter.Tendsto.eventually_const_lt hx (hL.tendsto x)
        have h1 : HasDerivAt (fun s : ℝ => c - (s - T0)) (-1) x := by
          simpa using ((hasDerivAt_id x).sub_const T0).const_sub c
        have hd := (h1.ofReal_comp.const_mul (Complex.I * u)).cexp
        have heq : (fun s : ℝ => Complex.exp (Complex.I * u * ((max (c - (s - T0)) 0 : ℝ) : ℂ)))
            =ᶠ[𝓝 x] (fun s : ℝ => Complex.exp (Complex.I * u * ((c - (s - T0) : ℝ) : ℂ))) := by
          filter_upwards [hev] with s hs
          rw [max_eq_left hs.le]
        refine ((hd.congr_of_eventuallyEq heq).hasDerivWithinAt).congr_deriv ?_
        beta_reduce
        rw [max_eq_left hx.le]
        unfold gf
        rw [Set.indicator_of_mem (show c - (x - T0) ∈ Set.Ioi (0:ℝ) from hx)]
        push_cast
        ring
      · push_neg at hx
        have hconst : HasDerivWithinAt
            (fun _ : ℝ => Complex.exp (Complex.I * u * ((0:ℝ) : ℂ))) 0 (Set.Ioi x) x :=
          hasDerivWithinAt_const _ _ _
        refine (hconst.congr (fun y hy => ?_) ?_).congr_deriv ?_
        · beta_reduce
          have hy' : x < y := hy
          rw [max_eq_right (show c - (y - T0) ≤ 0 by linarith)]
        · beta_reduce
          rw [max_eq_right hx]
        · beta_reduce
          rw [max_eq_right hx]
          unfold gf
          rw [Set.indicator_of_notMem (show (0:ℝ) ∉ Set.Ioi (0:ℝ) by simp), mul_zero]
    · refine (intervalIntegrable_const (c := ‖Complex.I * (u:ℂ)‖)).mono_fun'
        ((measurable_const.mul ((gf_meas u).comp hH.measurable)).aestronglyMeasurable)
        (ae_of_all _ (fun s => ?_))
      beta_reduce
      rw [norm_mul, norm_neg]
      exact mul_le_of_le_one_right (norm_nonneg _) (gf_norm u _)
  rw [intervalIntegral.integral_const_mul] at key
  exact key.symm

/-! ### Point-process bookkeeping -/

lemma exists_idx (N : PointProcess Ω) (ω : Ω) (t : ℝ) :
    ∃ n : ℤ, N.T n ω ≤ t ∧ t < N.T (n + 1) ω := by
  have hbot : ∃ z : ℤ, N.T z ω ≤ t :=
    ((N.tendsto_atBot ω).eventually (eventually_le_atBot t)).exists
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ n, n ≥ M → t < N.T n ω :=
    eventually_atTop.1 ((N.tendsto_atTop ω).eventually (eventually_gt_atTop t))
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, N.T z ω ≤ t → z ≤ b := by
    refine ⟨M, fun z hz => ?_⟩
    by_contra h
    have := hM z (by omega)
    linarith
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd hbot
  refine ⟨n, hn, ?_⟩
  by_contra h
  have := hmax (n + 1) (not_lt.1 h)
  omega

lemma W_nonneg (N : PointProcess Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (N.T n ω) (N.T (n + 1) ω) →
      W t ω = max (Wl (N.T n ω) ω + σ n ω - (t - N.T n ω)) 0) (t : ℝ) (ω : Ω) :
    0 ≤ W t ω := by
  obtain ⟨n, h1, h2⟩ := exists_idx N ω t
  rw [hlind n ω t ⟨h1, h2⟩]
  exact le_max_right _ _

lemma Wl_nonneg (N : PointProcess Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ)
    (hll : IsLeftLimitProcess W Wl)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (N.T n ω) (N.T (n + 1) ω) →
      W t ω = max (Wl (N.T n ω) ω + σ n ω - (t - N.T n ω)) 0) (s : ℝ) (ω : Ω) :
    0 ≤ Wl s ω :=
  ge_of_tendsto (hll s ω) (Eventually.of_forall (fun v => W_nonneg N σ W Wl hlind v ω))

lemma Wl_next (N : PointProcess Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ)
    (hll : IsLeftLimitProcess W Wl)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (N.T n ω) (N.T (n + 1) ω) →
      W t ω = max (Wl (N.T n ω) ω + σ n ω - (t - N.T n ω)) 0) (n : ℤ) (ω : Ω) :
    Wl (N.T (n + 1) ω) ω = max (Wl (N.T n ω) ω + σ n ω - (N.T (n + 1) ω - N.T n ω)) 0 := by
  have hlt : N.T n ω < N.T (n + 1) ω := N.strictMono ω (by omega)
  have hc : Continuous (fun s : ℝ => max (Wl (N.T n ω) ω + σ n ω - (s - N.T n ω)) 0) :=
    (continuous_const.sub (continuous_id.sub continuous_const)).max continuous_const
  have h2 : Tendsto (fun s : ℝ => max (Wl (N.T n ω) ω + σ n ω - (s - N.T n ω)) 0)
      (𝓝[<] (N.T (n + 1) ω))
      (𝓝 (max (Wl (N.T n ω) ω + σ n ω - (N.T (n + 1) ω - N.T n ω)) 0)) :=
    (hc.tendsto _).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s => W s ω) (𝓝[<] (N.T (n + 1) ω))
      (𝓝 (max (Wl (N.T n ω) ω + σ n ω - (N.T (n + 1) ω - N.T n ω)) 0)) := by
    refine Tendsto.congr' ?_ h2
    filter_upwards [Ioo_mem_nhdsLT hlt] with s hs
    exact (hlind n ω s ⟨hs.1.le, hs.2⟩).symm
  exact tendsto_nhds_unique (hll _ ω) h1

lemma Wl_comp (θ : Flow Ω) (W Wl : ℝ → Ω → ℝ) (hll : IsLeftLimitProcess W Wl)
    (hc : IsCompatible θ W) (t s : ℝ) (ω : Ω) : Wl t (θ s ω) = Wl (t + s) ω := by
  have hmap : Tendsto (fun v : ℝ => v + s) (𝓝[<] t) (𝓝[<] (t + s)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_id.add continuous_const).tendsto t).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : v < t := hv
      exact Set.mem_Iio.2 (by linarith)
  have h1 := (hll (t + s) ω).comp hmap
  have h2 : Tendsto (fun v => W v (θ s ω)) (𝓝[<] t) (𝓝 (Wl (t + s) ω)) := by
    refine Tendsto.congr (fun v => ?_) h1
    show W (v + s) ω = W v (θ s ω)
    exact (hc v s ω).symm
  exact tendsto_nhds_unique (hll t (θ s ω)) h2

/-! ### Measurability -/

noncomputable def qa (k : ℕ) (s : ℝ) : ℝ := (((⌊((k:ℝ) + 1) * s⌋ : ℤ) : ℝ) + 1) / ((k:ℝ) + 1)

lemma qa_gt (k : ℕ) (s : ℝ) : s < qa k s := by
  unfold qa
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [lt_div_iff₀ hk]
  have := Int.lt_floor_add_one (((k:ℝ) + 1) * s)
  nlinarith

lemma qa_le (k : ℕ) (s : ℝ) : qa k s ≤ s + 1 / ((k:ℝ) + 1) := by
  unfold qa
  have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [div_le_iff₀ hk]
  have h2 : (s + 1 / ((k:ℝ) + 1)) * ((k:ℝ) + 1) = s * ((k:ℝ) + 1) + 1 := by
    rw [add_mul, one_div, inv_mul_cancel₀ hk.ne']
  rw [h2]
  have := Int.floor_le (((k:ℝ) + 1) * s)
  nlinarith

lemma jointly_meas (W : ℝ → Ω → ℝ) (hm : ∀ t, Measurable (W t))
    (hrc : ∀ (s : ℝ) (ω : Ω), ContinuousWithinAt (fun u => W u ω) (Set.Ici s) s) :
    Measurable (fun p : ℝ × Ω => W p.1 p.2) := by
  have hq : ∀ s : ℝ, Tendsto (fun k : ℕ => qa k s) atTop (𝓝[≥] s) := by
    intro s
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun k => (qa_gt k s).le)⟩
    have hup : Tendsto (fun k : ℕ => s + 1 / ((k:ℝ) + 1)) atTop (𝓝 s) := by
      have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [add_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => (qa_gt k s).le) (fun k => qa_le k s)
  refine measurable_of_tendsto_metrizable (f := fun (k : ℕ) (p : ℝ × Ω) => W (qa k p.1) p.2)
    (fun k => ?_) ?_
  · have h1 : Measurable (fun p : Ω × ℤ => W ((((p.2 : ℤ) : ℝ) + 1) / ((k:ℝ) + 1)) p.1) :=
      measurable_from_prod_countable_left (fun z => hm ((((z : ℤ) : ℝ) + 1) / ((k:ℝ) + 1)))
    have h2 : Measurable (fun p : ℝ × Ω => (p.2, ⌊((k:ℝ) + 1) * p.1⌋)) :=
      measurable_snd.prodMk (Int.measurable_floor.comp (measurable_const.mul measurable_fst))
    exact h1.comp h2
  · exact tendsto_pi_nhds.2 (fun p => (hrc p.1 p.2).tendsto.comp (hq p.1))

lemma Wl_meas (W Wl : ℝ → Ω → ℝ) (hm : ∀ t, Measurable (W t)) (hll : IsLeftLimitProcess W Wl)
    (s : ℝ) : Measurable (Wl s) := by
  have ht : Tendsto (fun k : ℕ => s - 1 / ((k:ℝ) + 1)) atTop (𝓝[<] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun k => ?_)⟩
    · have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => s) atTop (𝓝 s)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rwa [sub_zero] at this
    · have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
      exact Set.mem_Iio.2 (by linarith)
  exact measurable_of_tendsto_metrizable (f := fun (k : ℕ) => W (s - 1 / ((k:ℝ) + 1)))
    (fun k => hm _) (tendsto_pi_nhds.2 (fun ω => (hll s ω).comp ht))

/-! ### Palm calculus -/

lemma T0_shift (N : PointProcess Ω) (θ : Flow Ω) (hc : N.Compatible θ) (n : ℤ) (ω : Ω) :
    N.T 0 (θ (N.T n ω) ω) = 0 := by
  obtain ⟨ω', hω'⟩ : ∃ ω', ω' = θ (N.T n ω) ω := ⟨_, rfl⟩
  rw [← hω']
  have h1 : N.count (θ (N.T n ω) ω) {0} = N.count ω ((fun s => s - N.T n ω) ⁻¹' {0}) :=
    hc _ ω {0} (measurableSet_singleton 0)
  rw [← hω'] at h1
  have h2 : (fun s => s - N.T n ω) ⁻¹' {(0:ℝ)} = {N.T n ω} := by
    ext x; simp [sub_eq_zero]
  have h3 : N.count ω {N.T n ω} ≠ 0 := by
    unfold PointProcess.count
    rw [Measure.sum_apply _ (measurableSet_singleton _)]
    intro h0
    have := ENNReal.tsum_eq_zero.1 h0 n
    simp [Measure.dirac_apply_of_mem (Set.mem_singleton (N.T n ω))] at this
  rw [h2] at h1
  have h4 : ∃ k : ℤ, N.T k ω' = 0 := by
    by_contra hne
    push_neg at hne
    apply h3
    rw [← h1]
    unfold PointProcess.count
    rw [Measure.sum_apply _ (measurableSet_singleton _)]
    refine ENNReal.tsum_eq_zero.2 (fun k => ?_)
    show Measure.dirac (N.T k ω') {0} = 0
    rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (show N.T k ω' ∉ ({0} : Set ℝ) by simpa using hne k)]
  obtain ⟨k, hk⟩ := h4
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have h5 : N.T k ω' < N.T 0 ω' := N.strictMono ω' hk0
    have h6 := N.zero_le ω'
    linarith
  · subst hk0; exact hk
  · have h5 : N.T 1 ω' ≤ N.T k ω' := (N.strictMono ω').monotone (by omega)
    have h6 := N.lt_one ω'
    linarith

lemma P0_T0 (S : PalmSetting Ω) : ∀ᵐ ω ∂S.P0, S.N.T 0 ω = 0 := by
  obtain ⟨hlam, -⟩ := S.intensity
  obtain ⟨-, hpalm⟩ := S.palm
  have hA : MeasurableSet {ω | S.N.T 0 ω ≠ 0} :=
    (measurableSet_eq_fun (S.N.measurable_T 0) measurable_const).compl
  have h := hpalm _ hA 1 one_pos
  have hz : ∀ (ω : Ω) (n : ℤ), Set.indicator {ω | S.N.T 0 ω ≠ 0} (fun _ => (1:ENNReal))
      (S.θ (S.N.T n ω) ω) = 0 := by
    intro ω n
    apply Set.indicator_of_notMem
    simp only [Set.mem_setOf_eq, not_not]
    exact T0_shift S.N S.θ S.compatible n ω
  simp only [hz, mul_zero, tsum_zero, lintegral_zero] at h
  rw [ae_iff]
  have hl : ENNReal.ofReal (S.lam * 1) ≠ 0 := by
    rw [mul_one]; exact (ENNReal.ofReal_pos.2 hlam).ne'
  exact (mul_eq_zero.1 h).resolve_left hl

lemma palm_tsum (S : PalmSetting Ω) (h : Ω → ℂ) (hm : Measurable h) (B : ℝ)
    (hB : ∀ ω, ‖h ω‖ ≤ B) :
    ∑' n : ℤ, ∫ ω, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
        h (S.θ (S.N.T n ω) ω) ∂S.P
      = (S.lam : ℂ) * ∫ ω, h ω ∂S.P0 := by
  obtain ⟨hlam, -⟩ := S.intensity
  obtain ⟨hP0, hpalm⟩ := S.palm
  haveI := S.isProb
  haveI := hP0
  have hφ : ∀ n : ℤ, Measurable (fun ω => S.θ (S.N.T n ω) ω) := fun n =>
    S.θ.measurable_uncurry.comp ((S.N.measurable_T n).prodMk measurable_id)
  have hB' : ∀ n : ℤ, MeasurableSet {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} := fun n =>
    S.N.measurable_T n measurableSet_Ioc
  have hindm : ∀ n : ℤ, Measurable
      (fun ω => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω)) :=
    fun n => (measurable_const.indicator measurableSet_Ioc).comp (S.N.measurable_T n)
  have hμ : Measure.sum (fun n : ℤ => (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map
      (fun ω => S.θ (S.N.T n ω) ω)) = ENNReal.ofReal S.lam • S.P0 := by
    ext A hA
    have hpA := hpalm A hA 1 one_pos
    rw [mul_one] at hpA
    have hmeasA : ∀ n : ℤ, AEMeasurable
        (fun ω => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω) *
          A.indicator (fun _ => (1:ENNReal)) (S.θ (S.N.T n ω) ω)) S.P := fun n =>
      ((hindm n).mul ((measurable_const.indicator hA).comp (hφ n))).aemeasurable
    rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul, hpA, lintegral_tsum hmeasA]
    refine tsum_congr (fun n => ?_)
    rw [Measure.map_apply (hφ n) hA, Measure.restrict_apply (hφ n hA),
      ← lintegral_indicator_one ((hφ n hA).inter (hB' n))]
    refine lintegral_congr (fun ω => ?_)
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1 <;> by_cases h2 : S.θ (S.N.T n ω) ω ∈ A <;>
      simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, h1, h2,
        Pi.one_apply, mul_one, mul_zero, zero_mul, and_true, and_false, true_and, false_and,
        if_true, if_false]
  have hint : Integrable h (Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω))) := by
    rw [hμ]
    exact (Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)).smul_measure
      ENNReal.ofReal_ne_top
  have e1 : ∫ ω, h ω ∂(Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω)))
      = (S.lam : ℂ) * ∫ ω, h ω ∂S.P0 := by
    rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal hlam.le, Complex.real_smul]
  have e2 : ∫ ω, h ω ∂(Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω)))
      = ∑' n : ℤ, ∫ ω, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
          h (S.θ (S.N.T n ω) ω) ∂S.P := by
    rw [integral_sum_measure hint]
    refine tsum_congr (fun n => ?_)
    rw [integral_map (hφ n).aemeasurable hm.aestronglyMeasurable, ← integral_indicator (hB' n)]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1
    · simp only [Set.indicator_of_mem h1, one_mul,
        Set.indicator_of_mem (show ω ∈ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1)]
    · simp only [Set.indicator_of_notMem h1, zero_mul,
        Set.indicator_of_notMem (show ω ∉ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1)]
  rw [← e2, e1]

lemma palm_integral (S : PalmSetting Ω) (h : Ω → ℂ) (hm : Measurable h) (B : ℝ)
    (hB : ∀ ω, ‖h ω‖ ≤ B) :
    ∫ ω, ∑' n : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
        h (S.θ (S.N.T n ω) ω) ∂S.P
      = (S.lam : ℂ) * ∫ ω, h ω ∂S.P0 := by
  obtain ⟨hlam, -⟩ := S.intensity
  obtain ⟨hP0, hpalm⟩ := S.palm
  haveI := S.isProb
  haveI := hP0
  have hφ : ∀ n : ℤ, Measurable (fun ω => S.θ (S.N.T n ω) ω) := fun n =>
    S.θ.measurable_uncurry.comp ((S.N.measurable_T n).prodMk measurable_id)
  have hB' : ∀ n : ℤ, MeasurableSet {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} := fun n =>
    S.N.measurable_T n measurableSet_Ioc
  have hindm : ∀ n : ℤ, Measurable
      (fun ω => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω)) :=
    fun n => (measurable_const.indicator measurableSet_Ioc).comp (S.N.measurable_T n)
  have hμ : Measure.sum (fun n : ℤ => (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map
      (fun ω => S.θ (S.N.T n ω) ω)) = ENNReal.ofReal S.lam • S.P0 := by
    ext A hA
    have hpA := hpalm A hA 1 one_pos
    rw [mul_one] at hpA
    have hmeasA : ∀ n : ℤ, AEMeasurable
        (fun ω => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω) *
          A.indicator (fun _ => (1:ENNReal)) (S.θ (S.N.T n ω) ω)) S.P := fun n =>
      ((hindm n).mul ((measurable_const.indicator hA).comp (hφ n))).aemeasurable
    rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul, hpA, lintegral_tsum hmeasA]
    refine tsum_congr (fun n => ?_)
    rw [Measure.map_apply (hφ n) hA, Measure.restrict_apply (hφ n hA),
      ← lintegral_indicator_one ((hφ n hA).inter (hB' n))]
    refine lintegral_congr (fun ω => ?_)
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1 <;> by_cases h2 : S.θ (S.N.T n ω) ω ∈ A <;>
      simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, h1, h2,
        Pi.one_apply, mul_one, mul_zero, zero_mul, and_true, and_false, true_and, false_and,
        if_true, if_false]
  have hint : Integrable h (Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω))) := by
    rw [hμ]
    exact (Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ hB)).smul_measure
      ENNReal.ofReal_ne_top
  have e1 : ∫ ω, h ω ∂(Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω)))
      = (S.lam : ℂ) * ∫ ω, h ω ∂S.P0 := by
    rw [hμ, integral_smul_measure, ENNReal.toReal_ofReal hlam.le, Complex.real_smul]
  have e2 : ∫ ω, h ω ∂(Measure.sum (fun n : ℤ =>
      (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map (fun ω => S.θ (S.N.T n ω) ω)))
      = ∑' n : ℤ, ∫ ω, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
          h (S.θ (S.N.T n ω) ω) ∂S.P := by
    rw [integral_sum_measure hint]
    refine tsum_congr (fun n => ?_)
    rw [integral_map (hφ n).aemeasurable hm.aestronglyMeasurable, ← integral_indicator (hB' n)]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1
    · simp only [Set.indicator_of_mem h1, one_mul,
        Set.indicator_of_mem (show ω ∈ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1)]
    · simp only [Set.indicator_of_notMem h1, zero_mul,
        Set.indicator_of_notMem (show ω ∉ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1)]
  have hFm : ∀ n : ℤ, AEStronglyMeasurable
      (fun ω => (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
        h (S.θ (S.N.T n ω) ω)) S.P := fun n =>
    (((measurable_const.indicator measurableSet_Ioc).comp (S.N.measurable_T n)).mul
      (hm.comp (hφ n))).aestronglyMeasurable
  have hsum : ∑' n : ℤ, ∫⁻ ω, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω) ∂S.P
      = ENNReal.ofReal S.lam := by
    have := hpalm Set.univ MeasurableSet.univ 1 one_pos
    simp only [Set.indicator_univ, mul_one, measure_univ] at this
    rw [this, lintegral_tsum (fun n => (hindm n).aemeasurable)]
  have hfin : ∑' n : ℤ, ∫⁻ ω, ‖(Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
      h (S.θ (S.N.T n ω) ω)‖ₑ ∂S.P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (b := ENNReal.ofReal B * ENNReal.ofReal S.lam) ?_
    rw [← hsum, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun n => ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun ω => ?_)
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1
    · simp only [Set.indicator_of_mem h1, one_mul, mul_one]
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · simp only [Set.indicator_of_notMem h1, zero_mul, mul_zero, enorm_zero, le_refl]
  have e3 : ∫ ω, ∑' n : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
        h (S.θ (S.N.T n ω) ω) ∂S.P
      = ∑' n : ℤ, ∫ ω, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
        h (S.θ (S.N.T n ω) ω) ∂S.P :=
    integral_tsum hFm hfin
  rw [e3, ← e2, e1]

lemma statW (S : PalmSetting Ω) (W : ℝ → Ω → ℝ) (hc : IsCompatible S.θ W) (f : ℝ → ℂ)
    (hf : Measurable f) (hW0 : Measurable (W 0)) (s : ℝ) :
    ∫ ω, f (W s ω) ∂S.P = ∫ ω, f (W 0 ω) ∂S.P := by
  have h1 : ∫ ω, f (W s ω) ∂S.P = ∫ ω, f (W 0 (S.θ s ω)) ∂S.P :=
    integral_congr_ae (ae_of_all _ (fun ω => by beta_reduce; rw [hc 0 s ω, zero_add]))
  have hmθ : Measurable (fun ω => S.θ s ω) := S.θ.measurable' s
  have h3 : Measure.map (fun ω => S.θ s ω) S.P = S.P := S.invariant s
  have h2 := integral_map (μ := S.P) hmθ.aemeasurable (hf.comp hW0).aestronglyMeasurable
  rw [h3] at h2
  rw [h1]
  exact h2.symm

/-! ### The pathwise rate-conservation identity -/

lemma pathwise (S : PalmSetting Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ) (u : ℝ)
    (hσ : ∀ n ω, 0 ≤ σ n ω)
    (hσmark : ∀ (n k : ℤ) (ω : Ω), σ n (S.θ (S.N.T k ω) ω) = σ (n + k) ω)
    (hll : IsLeftLimitProcess W Wl)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (S.N.T n ω) (S.N.T (n + 1) ω) →
      W t ω = max (Wl (S.N.T n ω) ω + σ n ω - (t - S.N.T n ω)) 0)
    (hWcomp : IsCompatible S.θ W) (hjm : Measurable (fun p : ℝ × Ω => W p.1 p.2)) (ω : Ω) :
    Complex.exp (Complex.I * u * W 1 ω) - Complex.exp (Complex.I * u * W 0 ω)
      = (∑' n : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ)) (S.N.T n ω) *
          (Complex.exp (Complex.I * u * Wl 0 (S.θ (S.N.T n ω) ω)) *
            (Complex.exp (Complex.I * u * σ 0 (S.θ (S.N.T n ω) ω)) - 1)))
        - Complex.I * u * ∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω) := by
  have hWs : Measurable (fun s => W s ω) := hjm.comp (measurable_id.prodMk measurable_const)
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun s => gf u (W s ω)) volume a b := fun a b =>
    (intervalIntegrable_const (c := (1:ℝ))).mono_fun' ((gf_meas u).comp hWs).aestronglyMeasurable
      (ae_of_all _ (fun s => gf_norm u _))
  have hpw : ∀ (m : ℤ) (a b : ℝ), S.N.T m ω ≤ a → a ≤ b → b ≤ S.N.T (m + 1) ω →
      ∫ s in a..b, gf u (W s ω)
        = ∫ s in a..b, gf u (max (Wl (S.N.T m ω) ω + σ m ω - (s - S.N.T m ω)) 0) := by
    intro m a b ha hab hb
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume b] with s hs hmem
    rw [Set.uIoc_of_le hab] at hmem
    rw [hlind m ω s ⟨ha.trans hmem.1.le, (lt_of_le_of_ne hmem.2 hs).trans_le hb⟩]
  have claim : ∀ n : ℕ, ∀ t : ℝ, max (S.N.T (n:ℤ) ω) 0 ≤ t → t ≤ S.N.T ((n:ℤ) + 1) ω →
      Complex.exp (Complex.I * u *
          ((max (Wl (S.N.T (n:ℤ) ω) ω + σ (n:ℤ) ω - (t - S.N.T (n:ℤ) ω)) 0 : ℝ) : ℂ))
        - Complex.exp (Complex.I * u * W 0 ω)
      = (∑ j ∈ Finset.Icc (1:ℤ) (n:ℤ), Complex.exp (Complex.I * u * Wl (S.N.T j ω) ω) *
            (Complex.exp (Complex.I * u * σ j ω) - 1))
        - Complex.I * u * ∫ s in (0:ℝ)..t, gf u (W s ω) := by
    intro n
    induction n with
    | zero =>
      intro t ht1 ht2
      simp only [Nat.cast_zero] at ht1 ht2 ⊢
      rw [max_eq_right (S.N.zero_le ω)] at ht1
      have hT1 : 0 < S.N.T (0 + 1) ω := by simpa using S.N.lt_one ω
      have e2 : W 0 ω = max (Wl (S.N.T 0 ω) ω + σ 0 ω - (0 - S.N.T 0 ω)) 0 :=
        hlind 0 ω 0 ⟨S.N.zero_le ω, hT1⟩
      have e1 := piece u (Wl (S.N.T 0 ω) ω + σ 0 ω) (S.N.T 0 ω) 0 t ht1
      have e3 := hpw 0 0 t (S.N.zero_le ω) ht1 ht2
      have e4 : (∑ j ∈ Finset.Icc (1:ℤ) 0, Complex.exp (Complex.I * u * Wl (S.N.T j ω) ω) *
          (Complex.exp (Complex.I * u * σ j ω) - 1)) = 0 := by
        rw [Finset.Icc_eq_empty (show ¬ ((1:ℤ) ≤ 0) by norm_num), Finset.sum_empty]
      rw [e4, e3]
      rw [← e2] at e1
      linear_combination e1
    | succ n ih =>
      intro t ht1 ht2
      have hc : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := Nat.cast_succ n
      rw [hc] at ht1 ht2 ⊢
      have hpos : 0 < S.N.T ((n:ℤ) + 1) ω :=
        lt_of_lt_of_le (S.N.lt_one ω) ((S.N.strictMono ω).monotone (by omega))
      rw [max_eq_left hpos.le] at ht1
      have hlt : S.N.T (n:ℤ) ω < S.N.T ((n:ℤ) + 1) ω := S.N.strictMono ω (by omega)
      have hih := ih (S.N.T ((n:ℤ) + 1) ω) (max_le hlt.le hpos.le) le_rfl
      rw [← Wl_next S.N σ W Wl hll hlind (n:ℤ) ω] at hih
      have hcnn : 0 ≤ Wl (S.N.T ((n:ℤ) + 1) ω) ω + σ ((n:ℤ) + 1) ω :=
        add_nonneg (Wl_nonneg S.N σ W Wl hll hlind _ ω) (hσ _ ω)
      have ep := piece u (Wl (S.N.T ((n:ℤ) + 1) ω) ω + σ ((n:ℤ) + 1) ω) (S.N.T ((n:ℤ) + 1) ω)
        (S.N.T ((n:ℤ) + 1) ω) t ht1
      rw [sub_self, sub_zero, max_eq_left hcnn] at ep
      have hJ : Complex.exp (Complex.I * u *
            ((Wl (S.N.T ((n:ℤ) + 1) ω) ω + σ ((n:ℤ) + 1) ω : ℝ) : ℂ))
          = Complex.exp (Complex.I * u * Wl (S.N.T ((n:ℤ) + 1) ω) ω) *
            Complex.exp (Complex.I * u * σ ((n:ℤ) + 1) ω) := by
        rw [← Complex.exp_add, Complex.ofReal_add, mul_add]
      have hS : Finset.Icc (1:ℤ) ((n:ℤ) + 1) = insert ((n:ℤ) + 1) (Finset.Icc 1 (n:ℤ)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hpw' := hpw ((n:ℤ) + 1) (S.N.T ((n:ℤ) + 1) ω) t le_rfl ht1 ht2
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hii 0 (S.N.T ((n:ℤ) + 1) ω)) (hii (S.N.T ((n:ℤ) + 1) ω) t)
      rw [hS, Finset.sum_insert (show ((n:ℤ) + 1) ∉ Finset.Icc (1:ℤ) (n:ℤ) by
        simp only [Finset.mem_Icc]; omega)]
      linear_combination ep + hJ + hih - (Complex.I * u) * hadd + (Complex.I * u) * hpw'
  obtain ⟨m, hm1, hm2⟩ := exists_idx S.N ω 1
  have hm0 : 0 ≤ m := by
    by_contra hneg
    have h1 : S.N.T (m + 1) ω ≤ S.N.T 0 ω := (S.N.strictMono ω).monotone (by omega)
    linarith [S.N.zero_le ω]
  lift m to ℕ using hm0 with k
  have hc := claim k 1 (max_le hm1 zero_le_one) hm2.le
  rw [← hlind (k:ℤ) ω 1 ⟨hm1, hm2⟩, intervalIntegral.integral_of_le zero_le_one] at hc
  rw [hc]
  congr 1
  symm
  rw [tsum_eq_sum (s := Finset.Icc 1 (k:ℤ))]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_Icc] at hj
    have hTpos : S.N.T j ω ∈ Set.Ioc (0:ℝ) 1 := by
      constructor
      · have h5 : S.N.T 1 ω ≤ S.N.T j ω := (S.N.strictMono ω).monotone hj.1
        linarith [S.N.lt_one ω]
      · have h5 : S.N.T j ω ≤ S.N.T (k:ℤ) ω := (S.N.strictMono ω).monotone hj.2
        linarith
    simp only [Set.indicator_of_mem hTpos, one_mul]
    rw [Wl_comp S.θ W Wl hll hWcomp 0 (S.N.T j ω) ω, zero_add, hσmark 0 j ω, zero_add]
  · intro n hn
    rw [Finset.mem_Icc] at hn
    have hnot : S.N.T n ω ∉ Set.Ioc (0:ℝ) 1 := by
      rintro ⟨h1, h2⟩
      by_cases hn1 : 1 ≤ n
      · have hn2 : (k:ℤ) + 1 ≤ n := by omega
        have h7 : S.N.T ((k:ℤ) + 1) ω ≤ S.N.T n ω := (S.N.strictMono ω).monotone hn2
        linarith
      · have hn0 : n ≤ 0 := by omega
        have h7 : S.N.T n ω ≤ S.N.T 0 ω := (S.N.strictMono ω).monotone hn0
        linarith [S.N.zero_le ω]
    rw [Set.indicator_of_notMem hnot, zero_mul]

/-! ### PASTA -/

lemma ioc_inter (a b c d : ℝ) :
    Set.Ioc a b ∩ Set.Ioc c d = Set.Ioc (max a c) (min b d) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, max_lt_iff, le_min_iff]
  tauto

lemma count_eq (N : PointProcess Ω) (ω : Ω) {B : Set ℝ} (hB : MeasurableSet B) :
    N.count ω B = ∑' n : ℤ, B.indicator (fun _ => (1:ENNReal)) (N.T n ω) := by
  unfold PointProcess.count
  rw [Measure.sum_apply _ hB]
  exact tsum_congr (fun n => Measure.dirac_apply' _ hB)

lemma count_meas (N : PointProcess Ω) {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun ω => N.count ω B) := by
  have h : (fun ω => N.count ω B)
      = fun ω => ∑' n : ℤ, B.indicator (fun _ => (1:ENNReal)) (N.T n ω) :=
    funext (fun ω => count_eq N ω hB)
  rw [h]
  exact Measurable.ennreal_tsum (fun n => (measurable_const.indicator hB).comp (N.measurable_T n))

noncomputable def mu1 (S : PalmSetting Ω) : Measure (ℝ × Ω) :=
  Measure.sum (fun n : ℤ => (S.P.restrict {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1}).map
    (fun ω => (S.N.T n ω, ω)))

noncomputable def mu2 (S : PalmSetting Ω) : Measure (ℝ × Ω) :=
  ENNReal.ofReal S.lam • (volume.restrict (Set.Ioc (0:ℝ) 1)).prod S.P

lemma mu1_rect (S : PalmSetting Ω) (a b : ℝ) (A : Set Ω) (hA : MeasurableSet A) :
    mu1 S (Set.Ioc a b ×ˢ A)
      = ∫⁻ ω, A.indicator (fun _ => (1:ENNReal)) ω *
          S.N.count ω (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1) ∂S.P := by
  have hψ : ∀ n : ℤ, Measurable (fun ω => (S.N.T n ω, ω)) := fun n =>
    (S.N.measurable_T n).prodMk measurable_id
  have hR : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hI : MeasurableSet (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1) :=
    measurableSet_Ioc.inter measurableSet_Ioc
  have hB' : ∀ n : ℤ, MeasurableSet {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} := fun n =>
    S.N.measurable_T n measurableSet_Ioc
  have hm : ∀ n : ℤ, AEMeasurable (fun ω => A.indicator (fun _ => (1:ENNReal)) ω *
      (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω)) S.P :=
    fun n => ((measurable_const.indicator hA).mul
      ((measurable_const.indicator hI).comp (S.N.measurable_T n))).aemeasurable
  have hcount : ∀ ω, A.indicator (fun _ => (1:ENNReal)) ω *
      S.N.count ω (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1)
      = ∑' n : ℤ, A.indicator (fun _ => (1:ENNReal)) ω *
          (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ENNReal)) (S.N.T n ω) := by
    intro ω
    rw [count_eq S.N ω hI, ENNReal.tsum_mul_left]
  rw [lintegral_congr hcount, lintegral_tsum hm, mu1, Measure.sum_apply _ hR]
  refine tsum_congr (fun n => ?_)
  rw [Measure.map_apply (hψ n) hR, Measure.restrict_apply ((hψ n) hR),
    ← lintegral_indicator_one (((hψ n) hR).inter (hB' n))]
  refine lintegral_congr (fun ω => ?_)
  by_cases h1 : S.N.T n ω ∈ Set.Ioc a b <;> by_cases h2 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1 <;>
    by_cases h3 : ω ∈ A <;>
    simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_setOf_eq, h1, h2, h3, Pi.one_apply, mul_one, mul_zero, zero_mul, and_true,
      and_false, true_and, false_and, if_true, if_false]

lemma mu1_univ (S : PalmSetting Ω) : mu1 S Set.univ = ENNReal.ofReal S.lam := by
  have h := mu1_rect S 0 1 Set.univ MeasurableSet.univ
  have hψ : ∀ n : ℤ, Measurable (fun ω => (S.N.T n ω, ω)) := fun n =>
    (S.N.measurable_T n).prodMk measurable_id
  have hU : mu1 S Set.univ = mu1 S (Set.Ioc 0 1 ×ˢ Set.univ) := by
    unfold mu1
    rw [Measure.sum_apply _ MeasurableSet.univ,
      Measure.sum_apply _ (measurableSet_Ioc.prod MeasurableSet.univ)]
    refine tsum_congr (fun n => ?_)
    rw [Measure.map_apply (hψ n) MeasurableSet.univ, Set.preimage_univ,
      Measure.map_apply (hψ n) (measurableSet_Ioc.prod MeasurableSet.univ),
      Measure.restrict_apply MeasurableSet.univ,
      Measure.restrict_apply ((hψ n) (measurableSet_Ioc.prod MeasurableSet.univ))]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, Set.mem_prod, Set.mem_setOf_eq,
      true_and, and_true, and_self]
  obtain ⟨-, hlamI⟩ := S.intensity
  rw [hU, h, Set.inter_self, hlamI]
  refine lintegral_congr (fun ω => ?_)
  simp only [Set.indicator_univ, one_mul]

lemma mu2_rect (S : PalmSetting Ω) (a b : ℝ) (A : Set Ω) :
    mu2 S (Set.Ioc a b ×ˢ A)
      = ENNReal.ofReal S.lam * (volume (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1) * S.P A) := by
  haveI := S.isProb
  rw [mu2, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    Measure.restrict_apply measurableSet_Ioc]

lemma mu2_univ (S : PalmSetting Ω) : mu2 S Set.univ = ENNReal.ofReal S.lam := by
  haveI := S.isProb
  rw [mu2, Measure.smul_apply, smul_eq_mul, ← Set.univ_prod_univ, Measure.prod_prod,
    Measure.restrict_apply_univ, Real.volume_Ioc, measure_univ, sub_zero, ENNReal.ofReal_one,
    mul_one, mul_one]

lemma rect_eq (S : PalmSetting Ω) (H : History Ω)
    (hint : HasConstantIntensity H S.N S.P S.lam) (a b : ℝ) (A : Set Ω)
    (hA : MeasurableSet[H.F a] A) :
    ∫⁻ ω, A.indicator (fun _ => (1:ENNReal)) ω *
        S.N.count ω (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1) ∂S.P
      = ENNReal.ofReal S.lam * (volume (Set.Ioc a b ∩ Set.Ioc (0:ℝ) 1) * S.P A) := by
  haveI := S.isProb
  obtain ⟨hlam, hlamI⟩ := S.intensity
  obtain ⟨-, hce⟩ := hint
  have hA0 : MeasurableSet A := H.le_top a A hA
  rw [ioc_inter]
  by_cases hab : min b 1 ≤ max a 0
  · rw [Set.Ioc_eq_empty (not_lt.2 hab)]
    simp only [measure_empty, mul_zero, zero_mul, lintegral_zero]
  · push_neg at hab
    have ha'0 : (0:ℝ) ≤ max a 0 := le_max_right _ _
    have hb'1 : min b 1 ≤ (1:ℝ) := min_le_right _ _
    have hA' : MeasurableSet[H.F (max a 0)] A := H.mono a (max a 0) (le_max_left _ _) A hA
    have hsub : Set.Ioc (max a 0) (min b 1) ⊆ Set.Ioc (0:ℝ) 1 := Set.Ioc_subset_Ioc ha'0 hb'1
    have hmeasC : Measurable (fun ω => S.N.count ω (Set.Ioc (max a 0) (min b 1))) :=
      count_meas S.N measurableSet_Ioc
    have hfin : ∫⁻ ω, S.N.count ω (Set.Ioc (max a 0) (min b 1)) ∂S.P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal S.lam) ENNReal.ofReal_ne_top ?_
      rw [hlamI]
      exact lintegral_mono (fun ω => measure_mono hsub)
    have hXint : Integrable (fun ω => (S.N.count ω (Set.Ioc (max a 0) (min b 1))).toReal) S.P :=
      integrable_toReal_of_lintegral_ne_top hmeasC.aemeasurable hfin
    have hce' := hce (max a 0) (min b 1) hab.le
    have h1 : ∫ ω in A, (S.N.count ω (Set.Ioc (max a 0) (min b 1))).toReal ∂S.P
        = S.lam * (min b 1 - max a 0) * (S.P A).toReal := by
      calc ∫ ω in A, (S.N.count ω (Set.Ioc (max a 0) (min b 1))).toReal ∂S.P
          = ∫ ω in A, (condExp (H.F (max a 0)) S.P
              (fun ω => (S.N.count ω (Set.Ioc (max a 0) (min b 1))).toReal)) ω ∂S.P :=
            (setIntegral_condExp (H.le_top (max a 0)) hXint hA').symm
        _ = ∫ ω in A, S.lam * (min b 1 - max a 0) ∂S.P :=
            integral_congr_ae (ae_restrict_of_ae hce')
        _ = S.lam * (min b 1 - max a 0) * (S.P A).toReal := by
            rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
    have hL : ∫⁻ ω, A.indicator (fun _ => (1:ENNReal)) ω *
        S.N.count ω (Set.Ioc (max a 0) (min b 1)) ∂S.P
        = ∫⁻ ω in A, S.N.count ω (Set.Ioc (max a 0) (min b 1)) ∂S.P := by
      rw [← lintegral_indicator hA0]
      refine lintegral_congr (fun ω => ?_)
      by_cases h : ω ∈ A
      · simp only [Set.indicator_of_mem h, one_mul]
      · simp only [Set.indicator_of_notMem h, zero_mul]
    have hfinA : ∫⁻ ω in A, S.N.count ω (Set.Ioc (max a 0) (min b 1)) ∂S.P ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
    have h2 : ∫ ω in A, (S.N.count ω (Set.Ioc (max a 0) (min b 1))).toReal ∂S.P
        = (∫⁻ ω in A, S.N.count ω (Set.Ioc (max a 0) (min b 1)) ∂S.P).toReal :=
      integral_toReal hmeasC.aemeasurable (ae_restrict_of_ae (ae_lt_top hmeasC hfin))
    rw [hL, ← ENNReal.ofReal_toReal hfinA, ← h2, h1, Real.volume_Ioc,
      ENNReal.ofReal_mul (mul_nonneg hlam.le (sub_nonneg.2 hab.le)), ENNReal.ofReal_mul hlam.le,
      ENNReal.ofReal_toReal (measure_ne_top S.P A), mul_assoc]

lemma Wl_eq_W (N : PointProcess Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ)
    (hll : IsLeftLimitProcess W Wl)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (N.T n ω) (N.T (n + 1) ω) →
      W t ω = max (Wl (N.T n ω) ω + σ n ω - (t - N.T n ω)) 0) (ω : Ω) (t : ℝ)
    (ht : t ∉ Set.range (fun n : ℤ => N.T n ω)) : Wl t ω = W t ω := by
  obtain ⟨n, h1, h2⟩ := exists_idx N ω t
  have h1' : N.T n ω < t := lt_of_le_of_ne h1 (fun h => ht ⟨n, h⟩)
  have hc : Continuous (fun s : ℝ => max (Wl (N.T n ω) ω + σ n ω - (s - N.T n ω)) 0) :=
    (continuous_const.sub (continuous_id.sub continuous_const)).max continuous_const
  have h3 : Tendsto (fun s => W s ω) (𝓝[<] t)
      (𝓝 (max (Wl (N.T n ω) ω + σ n ω - (t - N.T n ω)) 0)) := by
    refine Tendsto.congr' ?_ ((hc.tendsto t).mono_left nhdsWithin_le_nhds)
    filter_upwards [Ioo_mem_nhdsLT h1'] with s hs
    exact (hlind n ω s ⟨hs.1.le, hs.2.trans h2⟩).symm
  rw [tendsto_nhds_unique (hll t ω) h3, hlind n ω t ⟨h1, h2⟩]

lemma pasta (S : PalmSetting Ω) (σ : ℤ → Ω → ℝ) (W Wl : ℝ → Ω → ℝ) (H : History Ω)
    (hll : IsLeftLimitProcess W Wl)
    (hlind : ∀ (n : ℤ) (ω : Ω) (t : ℝ), t ∈ Set.Ico (S.N.T n ω) (S.N.T (n + 1) ω) →
      W t ω = max (Wl (S.N.T n ω) ω + σ n ω - (t - S.N.T n ω)) 0)
    (hWmeas : ∀ t, Measurable (W t)) (hWcomp : IsCompatible S.θ W)
    (hjm : Measurable (fun p : ℝ × Ω => W p.1 p.2))
    (hintensity : HasConstantIntensity H S.N S.P S.lam)
    (hpred : Measurable[H.predictableSigma] fun p : ℝ × Ω => Wl p.1 p.2)
    (f : ℝ → ℂ) (hf : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ 1) :
    ∫ ω, f (Wl 0 ω) ∂S.P0 = ∫ ω, f (W 0 ω) ∂S.P := by
  haveI := S.isProb
  obtain ⟨hlam, -⟩ := S.intensity
  obtain ⟨hP0, -⟩ := S.palm
  haveI := hP0
  have hle : H.predictableSigma ≤ (inferInstance : MeasurableSpace (ℝ × Ω)) := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨a, b, A, hA, rfl⟩
    exact measurableSet_Ioc.prod (H.le_top a A hA)
  have hWlm : Measurable (fun p : ℝ × Ω => Wl p.1 p.2) := hpred.mono hle le_rfl
  have hg : Measurable (fun p : ℝ × Ω => f (Wl p.1 p.2)) := hf.comp hWlm
  have hpi : IsPiSystem {s : Set (ℝ × Ω) | ∃ (a b : ℝ) (A : Set Ω),
      MeasurableSet[H.F a] A ∧ s = Set.Ioc a b ×ˢ A} := by
    rintro s ⟨a, b, A, hA, rfl⟩ t ⟨c, d, B, hB, rfl⟩ _
    refine ⟨max a c, min b d, A ∩ B, ?_, ?_⟩
    · exact (H.mono a (max a c) (le_max_left _ _) A hA).inter
        (H.mono c (max a c) (le_max_right _ _) B hB)
    · rw [Set.prod_inter_prod, ioc_inter]
  haveI : IsFiniteMeasure (mu1 S) := ⟨by rw [mu1_univ]; exact ENNReal.ofReal_lt_top⟩
  have htrim : (mu1 S).trim hle = (mu2 S).trim hle := by
    refine ext_of_generate_finite {s : Set (ℝ × Ω) | ∃ (a b : ℝ) (A : Set Ω),
      MeasurableSet[H.F a] A ∧ s = Set.Ioc a b ×ˢ A} rfl hpi ?_ ?_
    · rintro s ⟨a, b, A, hA, rfl⟩
      have hs : MeasurableSet[H.predictableSigma] (Set.Ioc a b ×ˢ A) :=
        MeasurableSpace.measurableSet_generateFrom ⟨a, b, A, hA, rfl⟩
      rw [trim_measurableSet_eq hle hs, trim_measurableSet_eq hle hs,
        mu1_rect S a b A (H.le_top a A hA), rect_eq S H hintensity a b A hA, mu2_rect]
    · rw [trim_measurableSet_eq hle MeasurableSet.univ,
        trim_measurableSet_eq hle MeasurableSet.univ, mu1_univ, mu2_univ]
  have hgsm : StronglyMeasurable[H.predictableSigma] (fun p : ℝ × Ω => f (Wl p.1 p.2)) :=
    (hf.comp hpred).stronglyMeasurable
  have hI12 : ∫ p, f (Wl p.1 p.2) ∂(mu1 S) = ∫ p, f (Wl p.1 p.2) ∂(mu2 S) := by
    rw [integral_trim hle hgsm, htrim, ← integral_trim hle hgsm]
  have hgint1 : Integrable (fun p : ℝ × Ω => f (Wl p.1 p.2)) (mu1 S) :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ (fun p => hfb _))
  have hψ : ∀ n : ℤ, Measurable (fun ω => (S.N.T n ω, ω)) := fun n =>
    (S.N.measurable_T n).prodMk measurable_id
  have hB' : ∀ n : ℤ, MeasurableSet {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} := fun n =>
    S.N.measurable_T n measurableSet_Ioc
  have hWl0 : Measurable (Wl 0) := Wl_meas W Wl hWmeas hll 0
  have hpt := palm_tsum S (fun ω => f (Wl 0 ω)) (hf.comp hWl0) 1 (fun ω => hfb _)
  beta_reduce at hpt
  have hL : ∫ p, f (Wl p.1 p.2) ∂(mu1 S) = (S.lam : ℂ) * ∫ ω, f (Wl 0 ω) ∂S.P0 := by
    rw [← hpt, mu1, integral_sum_measure hgint1]
    refine tsum_congr (fun n => ?_)
    rw [integral_map (hψ n).aemeasurable hg.aestronglyMeasurable, ← integral_indicator (hB' n)]
    refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
    by_cases h1 : S.N.T n ω ∈ Set.Ioc (0:ℝ) 1
    · simp only [Set.indicator_of_mem h1, one_mul,
        Set.indicator_of_mem (show ω ∈ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1),
        Wl_comp S.θ W Wl hll hWcomp 0, zero_add]
    · simp only [Set.indicator_of_notMem h1, zero_mul,
        Set.indicator_of_notMem (show ω ∉ {ω | S.N.T n ω ∈ Set.Ioc (0:ℝ) 1} from h1)]
  have hgint2 : Integrable (fun p : ℝ × Ω => f (Wl p.1 p.2))
      ((volume.restrict (Set.Ioc (0:ℝ) 1)).prod S.P) :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ (fun p => hfb _))
  have hgint3 : Integrable (Function.uncurry fun (ω : Ω) (t : ℝ) => f (W t ω))
      (S.P.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    Integrable.of_bound (hf.comp (hjm.comp measurable_swap)).aestronglyMeasurable 1
      (ae_of_all _ (fun p => hfb (W p.2 p.1)))
  have hcalc : ∫ t in Set.Ioc (0:ℝ) 1, ∫ ω, f (Wl t ω) ∂S.P = ∫ ω, f (W 0 ω) ∂S.P := by
    calc ∫ t in Set.Ioc (0:ℝ) 1, ∫ ω, f (Wl t ω) ∂S.P
        = ∫ ω, (∫ t in Set.Ioc (0:ℝ) 1, f (Wl t ω)) ∂S.P :=
          integral_integral_swap (f := fun (t : ℝ) (ω : Ω) => f (Wl t ω)) hgint2
      _ = ∫ ω, (∫ t in Set.Ioc (0:ℝ) 1, f (W t ω)) ∂S.P := by
          refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
          beta_reduce
          refine integral_congr_ae (ae_restrict_of_ae ?_)
          filter_upwards [(Set.countable_range (fun n : ℤ => S.N.T n ω)).ae_notMem volume]
            with t ht
          beta_reduce
          rw [Wl_eq_W S.N σ W Wl hll hlind ω t ht]
      _ = ∫ t in Set.Ioc (0:ℝ) 1, ∫ ω, f (W t ω) ∂S.P := integral_integral_swap hgint3
      _ = ∫ t in Set.Ioc (0:ℝ) 1, ∫ ω, f (W 0 ω) ∂S.P :=
          integral_congr_ae (ae_of_all _ (fun t => statW S W hWcomp f hf (hWmeas 0) t))
      _ = ∫ ω, f (W 0 ω) ∂S.P := by
          rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
            ENNReal.ofReal_one, ENNReal.toReal_one, one_smul]
  have hR : ∫ p, f (Wl p.1 p.2) ∂(mu2 S) = (S.lam : ℂ) * ∫ ω, f (W 0 ω) ∂S.P := by
    rw [mu2, integral_smul_measure, ENNReal.toReal_ofReal hlam.le, Complex.real_smul,
      integral_prod _ hgint2]
    exact congrArg (fun z => (S.lam : ℂ) * z) hcalc
  have hlamC : (S.lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam.ne'
  exact mul_left_cancel₀ hlamC (hL.symm.trans (hI12.trans hR))

/-! ### The denominator does not vanish -/

lemma denom_ne (P : Measure Ω) [IsProbabilityMeasure P] (σ0 : Ω → ℝ) (hσ : Measurable σ0)
    (lam u : ℝ) (hlam : 0 < lam) (hu : u ≠ 0) :
    Complex.I * u - (lam : ℂ) * ((∫ ω, Complex.exp (Complex.I * u * σ0 ω) ∂P) - 1) ≠ 0 := by
  intro hD
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = ∫ ω, Complex.exp (Complex.I * u * σ0 ω) ∂P := ⟨_, rfl⟩
  rw [← hχ] at hD
  have hre : χ.re = 1 := by
    have h := congrArg Complex.re hD
    simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.zero_re] at h
    have h2 : lam * (χ.re - 1) = 0 := by linarith
    have h3 := (mul_eq_zero.1 h2).resolve_left hlam.ne'
    linarith
  have hcos : ∀ ω, (Complex.exp (Complex.I * u * σ0 ω)).re = Real.cos (u * σ0 ω) := by
    intro ω
    rw [show Complex.I * (u:ℂ) * (σ0 ω : ℂ) = ((u * σ0 ω : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  have hsin : ∀ ω, (Complex.exp (Complex.I * u * σ0 ω)).im = Real.sin (u * σ0 ω) := by
    intro ω
    rw [show Complex.I * (u:ℂ) * (σ0 ω : ℂ) = ((u * σ0 ω : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_im _
  have hi : Integrable (fun ω => Complex.exp (Complex.I * u * σ0 ω)) P :=
    Integrable.of_bound ((measurable_cexp u).comp hσ).aestronglyMeasurable 1
      (ae_of_all _ (fun ω => (norm_cexp u _).le))
  have hcm : Measurable (fun ω => Real.cos (u * σ0 ω)) :=
    Real.measurable_cos.comp (measurable_const.mul hσ)
  have hci : Integrable (fun ω => Real.cos (u * σ0 ω)) P :=
    Integrable.of_bound hcm.aestronglyMeasurable 1
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _))
  have hreint : χ.re = ∫ ω, Real.cos (u * σ0 ω) ∂P := by
    rw [hχ, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hi]
    exact integral_congr_ae (ae_of_all _ (fun ω => by
      beta_reduce; rw [Complex.reCLM_apply]; exact hcos ω))
  have hcos1 : ∀ᵐ ω ∂P, Real.cos (u * σ0 ω) = 1 := by
    have hnn : 0 ≤ (fun ω => 1 - Real.cos (u * σ0 ω)) := fun ω => by
      have := Real.cos_le_one (u * σ0 ω)
      simp only [Pi.zero_apply]
      linarith
    have hint1 : Integrable (fun ω => 1 - Real.cos (u * σ0 ω)) P :=
      (integrable_const (1:ℝ)).sub hci
    have h0 : ∫ ω, (1 - Real.cos (u * σ0 ω)) ∂P = 0 := by
      rw [integral_sub (integrable_const (1:ℝ)) hci, integral_const, probReal_univ, one_smul,
        ← hreint, hre, sub_self]
    have := (integral_eq_zero_iff_of_nonneg hnn hint1).1 h0
    filter_upwards [this] with ω hω
    simp only [Pi.zero_apply] at hω
    linarith
  have hexp1 : ∀ᵐ ω ∂P, Complex.exp (Complex.I * u * σ0 ω) = 1 := by
    filter_upwards [hcos1] with ω hω
    have hs2 : Real.sin (u * σ0 ω) ^ 2 = 0 := by
      have := Real.sin_sq_add_cos_sq (u * σ0 ω)
      rw [hω] at this
      linarith
    have hs : Real.sin (u * σ0 ω) = 0 := (pow_eq_zero_iff two_ne_zero).1 hs2
    apply Complex.ext
    · rw [hcos ω, hω, Complex.one_re]
    · rw [hsin ω, hs, Complex.one_im]
  have hχ1 : χ = 1 := by
    rw [hχ, integral_congr_ae hexp1, integral_const, probReal_univ, one_smul]
  rw [hχ1, sub_self, mul_zero, sub_zero] at hD
  rcases mul_eq_zero.1 hD with h | h
  · exact Complex.I_ne_zero h
  · exact hu (Complex.ofReal_eq_zero.1 h)

theorem takacs_core (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ)
    (hW : IsWorkload Q W Wl) (hWmeas : ∀ t, Measurable (W t))
    (hWcomp : IsCompatible Q.toPalmSetting.θ W)
    (hstable : Q.rho < 1)
    (hindep : ∀ n : ℤ, ProbabilityTheory.IndepFun (Q.sigma n)
      (fun ω => Wl (Q.toPalmSetting.N.T n ω) ω) Q.toPalmSetting.P0)
    (hGI : ∀ u : ℝ,
      (∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P0)
        = ∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P)
    (hidle : (Q.toPalmSetting.P {ω | W 0 ω = 0}).toReal = 1 - Q.rho)
    (u : ℝ) :
    Complex.I * u * ∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P
      = (Q.toPalmSetting.lam : ℂ)
          * (∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0)
          * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1)
        + Complex.I * u * ((1 : ℂ) - (Q.rho : ℂ)) := by
  obtain ⟨hrc, hll, hlind⟩ := hW
  obtain ⟨hσm, hσmark⟩ := Q.sigma_marks
  haveI := Q.toPalmSetting.isProb
  obtain ⟨hP0, -⟩ := Q.toPalmSetting.palm
  haveI := hP0
  have hjm := jointly_meas W hWmeas hrc
  have hWl0 : Measurable (Wl 0) := Wl_meas W Wl hWmeas hll 0
  have hpath := fun ω => pathwise Q.toPalmSetting Q.sigma W Wl u Q.sigma_nonneg
    hσmark hll hlind hWcomp hjm ω
  have hJm : Measurable (fun ω => Complex.exp (Complex.I * u * Wl 0 ω) *
      (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1)) :=
    ((measurable_cexp u).comp hWl0).mul
      (((measurable_cexp u).comp (hσm 0)).sub measurable_const)
  have hJb : ∀ ω, ‖Complex.exp (Complex.I * u * Wl 0 ω) *
      (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1)‖ ≤ 2 := by
    intro ω
    rw [norm_mul, norm_cexp, one_mul]
    calc ‖Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1‖
        ≤ ‖Complex.exp (Complex.I * u * Q.sigma 0 ω)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_cexp, norm_one]; norm_num
  have hpalmJ := palm_integral Q.toPalmSetting _ hJm 2 hJb
  beta_reduce at hpalmJ
  have hint : ∀ t : ℝ, Integrable (fun ω => Complex.exp (Complex.I * u * W t ω))
      Q.toPalmSetting.P := fun t =>
    Integrable.of_bound ((measurable_cexp u).comp (hWmeas t)).aestronglyMeasurable 1
      (ae_of_all _ (fun ω => (norm_cexp u _).le))
  have hF : Integrable (Function.uncurry fun (ω : Ω) (s : ℝ) => gf u (W s ω))
      (Q.toPalmSetting.P.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    Integrable.of_bound ((gf_meas u).comp (hjm.comp measurable_swap)).aestronglyMeasurable
      1 (ae_of_all _ (fun p => gf_norm u (W p.2 p.1)))
  have hIGint : Integrable (fun ω => ∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω))
      Q.toPalmSetting.P := hF.integral_prod_left
  have hst : ∀ (f : ℝ → ℂ), Measurable f → ∀ t : ℝ,
      ∫ ω, f (W t ω) ∂Q.toPalmSetting.P = ∫ ω, f (W 0 ω) ∂Q.toPalmSetting.P :=
    fun f hf t => statW Q.toPalmSetting W hWcomp f hf (hWmeas 0) t
  have hA : ∫ ω, Complex.exp (Complex.I * u * W 1 ω) ∂Q.toPalmSetting.P
      = ∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P :=
    hst (fun x => Complex.exp (Complex.I * u * x)) (measurable_cexp u) 1
  have hIG : ∫ ω, (∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω)) ∂Q.toPalmSetting.P
      = ∫ ω, gf u (W 0 ω) ∂Q.toPalmSetting.P := by
    rw [integral_integral_swap hF]
    have hin : ∀ s : ℝ, ∫ ω, gf u (W s ω) ∂Q.toPalmSetting.P
        = ∫ ω, gf u (W 0 ω) ∂Q.toPalmSetting.P :=
      fun s => hst (gf u) (gf_meas u) s
    have hcongr : ∫ s in Set.Ioc (0:ℝ) 1, (∫ ω, gf u (W s ω) ∂Q.toPalmSetting.P)
        = ∫ s in Set.Ioc (0:ℝ) 1, (∫ ω, gf u (W 0 ω) ∂Q.toPalmSetting.P) :=
      integral_congr_ae (ae_of_all _ hin)
    rw [hcongr, setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.ofReal_one, ENNReal.toReal_one, one_smul]
  have hZ : MeasurableSet {ω | W 0 ω = 0} := measurableSet_eq_fun (hWmeas 0) measurable_const
  have hg0 : ∀ ω, gf u (W 0 ω) = Complex.exp (Complex.I * u * W 0 ω)
      - (({ω | W 0 ω = 0}.indicator (fun _ => (1:ℝ)) ω : ℝ) : ℂ) := by
    intro ω
    by_cases h : W 0 ω = 0
    · rw [Set.indicator_of_mem (show ω ∈ {ω | W 0 ω = 0} from h)]
      unfold gf
      rw [Set.indicator_of_notMem (show W 0 ω ∉ Set.Ioi (0:ℝ) by
        rw [h, Set.mem_Ioi]; exact lt_irrefl 0), h]
      simp
    · have hp : 0 < W 0 ω :=
        lt_of_le_of_ne (W_nonneg Q.toPalmSetting.N Q.sigma W Wl hlind 0 ω) (Ne.symm h)
      rw [Set.indicator_of_notMem (show ω ∉ {ω | W 0 ω = 0} from h)]
      unfold gf
      rw [Set.indicator_of_mem (show W 0 ω ∈ Set.Ioi (0:ℝ) from hp)]
      simp
  have hindint : Integrable (fun ω => (({ω | W 0 ω = 0}.indicator (fun _ => (1:ℝ)) ω : ℝ) : ℂ))
      Q.toPalmSetting.P := ((integrable_const (1:ℝ)).indicator hZ).ofReal
  have hE0 : ∫ ω, gf u (W 0 ω) ∂Q.toPalmSetting.P
      = ∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P - (1 - (Q.rho : ℂ)) := by
    rw [integral_congr_ae (ae_of_all _ hg0), integral_sub (hint 0) hindint, integral_complex_ofReal,
      integral_indicator_const _ hZ, smul_eq_mul, mul_one, measureReal_def, hidle,
      Complex.ofReal_sub, Complex.ofReal_one]
  have hT0 := P0_T0 Q.toPalmSetting
  have hY : (fun ω => Wl (Q.toPalmSetting.N.T 0 ω) ω) =ᵐ[Q.toPalmSetting.P0] Wl 0 := by
    filter_upwards [hT0] with ω hω
    rw [hω]
  have hind0 : ProbabilityTheory.IndepFun (Q.sigma 0) (Wl 0) Q.toPalmSetting.P0 :=
    (hindep 0).congr (Filter.EventuallyEq.refl _ _) hY
  have hind1 := hind0.comp (φ := fun x : ℝ => Complex.exp (Complex.I * u * x) - 1)
    (ψ := fun x : ℝ => Complex.exp (Complex.I * u * x))
    ((measurable_cexp u).sub measurable_const) (measurable_cexp u)
  have hmul : ∫ ω, (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) *
        Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0
      = (∫ ω, (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) ∂Q.toPalmSetting.P0) *
        ∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0 :=
    hind1.integral_fun_mul_eq_mul_integral
      (((measurable_cexp u).sub measurable_const).comp (hσm 0)).aestronglyMeasurable
      ((measurable_cexp u).comp hWl0).aestronglyMeasurable
  have hsub : ∫ ω, (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) ∂Q.toPalmSetting.P0
      = (∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P0) - 1 := by
    have hi : Integrable (fun ω => Complex.exp (Complex.I * u * Q.sigma 0 ω)) Q.toPalmSetting.P0 :=
      Integrable.of_bound ((measurable_cexp u).comp (hσm 0)).aestronglyMeasurable 1
        (ae_of_all _ (fun ω => (norm_cexp u _).le))
    have := integral_sub hi (integrable_const (1:ℂ))
    rw [integral_const, probReal_univ, one_smul] at this
    exact this
  have hJ0 : ∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) *
        (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) ∂Q.toPalmSetting.P0
      = ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1) *
        ∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0 := by
    have e1 : ∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) *
          (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) ∂Q.toPalmSetting.P0
        = ∫ ω, (Complex.exp (Complex.I * u * Q.sigma 0 ω) - 1) *
          Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0 :=
      integral_congr_ae (ae_of_all _ (fun ω => mul_comm _ _))
    rw [e1, hmul, hsub, hGI u]
  have hpt : ∀ ω, (∑' n : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ))
          (Q.toPalmSetting.N.T n ω) *
          (Complex.exp (Complex.I * u * Wl 0 (Q.toPalmSetting.θ (Q.toPalmSetting.N.T n ω) ω)) *
            (Complex.exp (Complex.I * u *
              Q.sigma 0 (Q.toPalmSetting.θ (Q.toPalmSetting.N.T n ω) ω)) - 1)))
      = (Complex.exp (Complex.I * u * W 1 ω) - Complex.exp (Complex.I * u * W 0 ω))
        + Complex.I * u * ∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω) := by
    intro ω
    rw [hpath ω]
    ring
  have hJsum : ∫ ω, (∑' n : ℤ, (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℂ))
          (Q.toPalmSetting.N.T n ω) *
          (Complex.exp (Complex.I * u * Wl 0 (Q.toPalmSetting.θ (Q.toPalmSetting.N.T n ω) ω)) *
            (Complex.exp (Complex.I * u *
              Q.sigma 0 (Q.toPalmSetting.θ (Q.toPalmSetting.N.T n ω) ω)) - 1))) ∂Q.toPalmSetting.P
      = (∫ ω, Complex.exp (Complex.I * u * W 1 ω) ∂Q.toPalmSetting.P
          - ∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P)
        + Complex.I * u * ∫ ω, (∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω))
            ∂Q.toPalmSetting.P := by
    have hint10 : Integrable (fun ω => Complex.exp (Complex.I * u * W 1 ω)
        - Complex.exp (Complex.I * u * W 0 ω)) Q.toPalmSetting.P := (hint 1).sub (hint 0)
    have hIGc : Integrable (fun ω => Complex.I * u *
        ∫ s in Set.Ioc (0:ℝ) 1, gf u (W s ω)) Q.toPalmSetting.P :=
      hIGint.const_mul _
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hint10 hIGc,
      integral_sub (hint 1) (hint 0), integral_const_mul]
  rw [hpalmJ, hJ0, hIG, hE0, hA] at hJsum
  linear_combination -hJsum

end Aux_pk

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ) (H : History Ω)
    (hW : IsWorkload Q W Wl) (hWmeas : ∀ t, Measurable (W t))
    (hWcomp : IsCompatible Q.toPalmSetting.θ W)
    (hstable : Q.rho < 1)
    (hhist : H.IsHistoryOf Q.toPalmSetting.N)
    (hintensity : HasConstantIntensity H Q.toPalmSetting.N Q.toPalmSetting.P Q.toPalmSetting.lam)
    (hpred : Measurable[H.predictableSigma] fun p : ℝ × Ω => Wl p.1 p.2)
    (hindep : ∀ n : ℤ, ProbabilityTheory.IndepFun (Q.sigma n)
      (fun ω => Wl (Q.toPalmSetting.N.T n ω) ω) Q.toPalmSetting.P0)
    (hidle : (Q.toPalmSetting.P {ω | W 0 ω = 0}).toReal = 1 - Q.rho)
    (hGI : ∀ u : ℝ,
      (∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P0)
        = ∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P)
    (u : ℝ) (hu : u ≠ 0) :
    Complex.I * u
        - (Q.toPalmSetting.lam : ℂ)
          * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1) ≠ 0 ∧
    (∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P)
      = (Complex.I * u * ((1 : ℂ) - (Q.rho : ℂ)))
        / (Complex.I * u
            - (Q.toPalmSetting.lam : ℂ)
              * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1)) := by
  have hT := Aux_pk.takacs_core Q W Wl hW hWmeas hWcomp hstable hindep hGI hidle u
  obtain ⟨hrc, hll, hlind⟩ := hW
  obtain ⟨hσm, -⟩ := Q.sigma_marks
  haveI := Q.toPalmSetting.isProb
  obtain ⟨hlam, -⟩ := Q.toPalmSetting.intensity
  have hjm := Aux_pk.jointly_meas W hWmeas hrc
  have hD := Aux_pk.denom_ne Q.toPalmSetting.P (Q.sigma 0) (hσm 0) Q.toPalmSetting.lam u hlam hu
  have hPA := Aux_pk.pasta Q.toPalmSetting Q.sigma W Wl H hll hlind hWmeas hWcomp hjm hintensity
    hpred (fun x => Complex.exp (Complex.I * u * x)) (Aux_pk.measurable_cexp u)
    (fun x => (Aux_pk.norm_cexp u x).le)
  beta_reduce at hPA
  refine ⟨hD, ?_⟩
  rw [eq_div_iff hD]
  rw [hPA] at hT
  linear_combination hT
