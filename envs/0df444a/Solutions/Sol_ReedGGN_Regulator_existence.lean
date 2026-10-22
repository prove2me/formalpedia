-- Prove2me | solution 1 for ReedGGN.Regulator.existence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:51:33.064379+00:00
-- url     : https://prove2.me/submissions/41f5b2d9-d731-426a-b51c-8ade5884c839

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation



namespace ReedGGN.Regulator

open MeasureTheory Filter Topology

theorem g47_cadlag_bdd {x : ℝ → ℝ} (hx : IsCadlag x) (T : ℝ) :
    ∃ M, ∀ s ∈ Set.Icc 0 T, |x s| ≤ M := by
  have hK : IsCompact (Set.Icc (0:ℝ) T) := isCompact_Icc
  refine hK.induction_on (p := fun S => ∃ M, ∀ s ∈ S, |x s| ≤ M) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro s t hst ⟨M, hM⟩; exact ⟨M, fun y hy => hM y (hst hy)⟩
  · intro s t ⟨M, hM⟩ ⟨N, hN⟩
    exact ⟨max M N, fun y hy => hy.elim (fun h => (hM y h).trans (le_max_left _ _))
      (fun h => (hN y h).trans (le_max_right _ _))⟩
  · intro t ht
    have h1 : ∀ᶠ y in nhdsWithin t (Set.Ici t), |x y| ≤ |x t| + 1 := by
      have h2 : ∀ᶠ y in nhdsWithin t (Set.Ici t), dist (x y) (x t) < 1 :=
        (hx.1 t ht.1).tendsto (Metric.ball_mem_nhds _ one_pos)
      filter_upwards [h2] with y hy
      rw [Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub (x y) (x t)
      linarith
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      exact ⟨_, nhdsWithin_mono _ (fun y hy => hy.1) h1, |x 0| + 1, fun y hy => hy⟩
    · obtain ⟨l, hl⟩ := hx.2 t hpos
      have h3 : ∀ᶠ y in nhdsWithin t (Set.Iio t), |x y| ≤ |l| + 1 := by
        have h2 : ∀ᶠ y in nhdsWithin t (Set.Iio t), dist (x y) l < 1 :=
          hl (Metric.ball_mem_nhds _ one_pos)
        filter_upwards [h2] with y hy
        rw [Real.dist_eq] at hy
        have := abs_sub_abs_le_abs_sub (x y) l
        linarith
      have hS : {y | |x y| ≤ max (|x t| + 1) (|l| + 1)} ∈ nhds t := by
        have hu : Set.Ici t ∪ Set.Iio t = Set.univ := by ext y; simp [le_or_gt]
        have : nhds t = nhdsWithin t (Set.Ici t ∪ Set.Iio t) := by rw [hu, nhdsWithin_univ]
        rw [this, nhdsWithin_union]
        exact ⟨h1.mono fun y hy => le_max_of_le_left hy, h3.mono fun y hy => le_max_of_le_right hy⟩
      exact ⟨_, mem_nhdsWithin_of_mem_nhds hS, _, fun y hy => hy⟩

theorem g47_q_bounds (s : ℝ) (n : ℕ) :
    s ≤ (⌈s * 2^n⌉ : ℝ) / 2^n ∧ (⌈s * 2^n⌉ : ℝ) / 2^n < s + 1 / 2^n := by
  have hp : (0:ℝ) < 2^n := by positivity
  constructor
  · rw [le_div_iff₀ hp]; exact Int.le_ceil _
  · rw [div_lt_iff₀ hp, add_mul, one_div_mul_cancel hp.ne']; exact Int.ceil_lt_add_one _

theorem g47_tendsto_inv_pow : Tendsto (fun n : ℕ => (1:ℝ) / 2^n) atTop (𝓝 0) := by
  have := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine this.congr (fun n => ?_)
  rw [div_pow, one_pow]

theorem g47_q_tendsto (s : ℝ) :
    Tendsto (fun n : ℕ => (⌈s * 2^n⌉ : ℝ) / 2^n) atTop (𝓝[≥] s) := by
  apply tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (g47_q_bounds s n).1⟩
  have hu : Tendsto (fun n : ℕ => s + 1 / 2^n) atTop (𝓝 s) := by
    have := (tendsto_const_nhds (x := s)).add g47_tendsto_inv_pow
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (g47_q_bounds s n).1) (fun n => (g47_q_bounds s n).2.le)

theorem g47_cadlag_meas {x : ℝ → ℝ} (hx : IsCadlag x) : Measurable (fun s => x (max s 0)) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n s => x (max ((⌈s * 2^n⌉ : ℝ) / 2^n) 0)) ?_ ?_
  · intro n
    have : (fun s : ℝ => x (max ((⌈s * 2^n⌉ : ℝ) / 2^n) 0)) =
        (fun k : ℤ => x (max ((k:ℝ) / 2^n) 0)) ∘ (fun s : ℝ => ⌈s * 2^n⌉) := rfl
    rw [this]
    exact (Measurable.of_discrete).comp (Int.measurable_ceil.comp (measurable_id.mul_const _))
  · rw [tendsto_pi_nhds]; intro s
    rcases le_or_gt 0 s with hs | hs
    · rw [max_eq_left hs]
      have h1 := (hx.1 s hs).tendsto.comp (g47_q_tendsto s)
      refine h1.congr' ?_
      filter_upwards with n
      simp only [Function.comp]
      rw [max_eq_left (hs.trans (g47_q_bounds s n).1)]
    · rw [max_eq_right hs.le]
      have : ∀ᶠ n in atTop, (⌈s * 2^n⌉ : ℝ) / 2^n < 0 := by
        have h := (tendsto_order.1 g47_tendsto_inv_pow).2 (-s) (by linarith)
        filter_upwards [h] with n hn
        linarith [(g47_q_bounds s n).2]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [this] with n hn
      rw [max_eq_right hn.le]

theorem g47_le_supNorm {f : ℝ → ℝ} {T M : ℝ} (hM : ∀ s ∈ Set.Icc 0 T, |f s| ≤ M) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) : |f s| ≤ supNorm T f := by
  unfold supNorm
  exact le_ciSup (f := fun r : Set.Icc (0:ℝ) T => |f r|)
    ⟨M, by rintro _ ⟨r, rfl⟩; exact hM r r.2⟩ ⟨s, hs⟩

theorem g47_supNorm_le {f : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T) (h : ∀ s ∈ Set.Icc 0 T, |f s| ≤ C) :
    supNorm T f ≤ C := by
  unfold supNorm
  haveI : Nonempty (Set.Icc (0:ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  exact ciSup_le fun r => h r r.2

theorem g47_supNorm_nonneg (T : ℝ) (f : ℝ → ℝ) : 0 ≤ supNorm T f :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem g47_sub_bdd {z₁ z₂ : ℝ → ℝ} (h₁ : IsCadlag z₁) (h₂ : IsCadlag z₂) (T : ℝ) :
    ∃ M, ∀ s ∈ Set.Icc 0 T, |(z₂ - z₁) s| ≤ M := by
  obtain ⟨M1, hM1⟩ := g47_cadlag_bdd h₁ T
  obtain ⟨M2, hM2⟩ := g47_cadlag_bdd h₂ T
  refine ⟨M2 + M1, fun s hs => ?_⟩
  simp only [Pi.sub_apply]
  have := abs_sub (z₂ s) (z₁ s)
  linarith [hM1 s hs, hM2 s hs]

theorem g47_integrand_eq (z : ℝ → ℝ) (a t : ℝ) (μ : Measure ℝ) :
    ∫ s in Set.Icc 0 t, max (z (t - s) + a) 0 ∂μ =
      ∫ s in Set.Icc 0 t, max (z (max (t - s) 0) + a) 0 ∂μ :=
  setIntegral_congr_fun measurableSet_Icc (fun s hs => by
    rw [max_eq_left (by linarith [hs.2] : (0:ℝ) ≤ t - s)])

theorem g47_comp_meas {z : ℝ → ℝ} (hz : IsCadlag z) (t : ℝ) :
    Measurable (fun s => z (max (t - s) 0)) :=
  (g47_cadlag_meas hz).comp (measurable_const.sub measurable_id)

theorem g47_integrable_F (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℝ → ℝ} (hz : IsCadlag z)
    (a t : ℝ) :
    Integrable (fun s => max (z (max (t - s) 0) + a) 0) (μ.restrict (Set.Icc 0 t)) := by
  obtain ⟨M, hM⟩ := g47_cadlag_bdd hz t
  refine Integrable.of_bound (((g47_comp_meas hz t).add_const a).max measurable_const).aestronglyMeasurable
    (M + |a|) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  have h1 := hM (max (t - s) 0) ⟨le_max_right _ _, by
    rw [max_le_iff]; exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩⟩
  rw [Real.norm_eq_abs]
  have h2 : |max (z (max (t - s) 0) + a) 0| ≤ |z (max (t - s) 0) + a| := by
    have := abs_max_sub_max_le_abs (z (max (t - s) 0) + a) 0 0
    simpa using this
  have h3 := abs_add_le (z (max (t - s) 0)) a
  linarith

theorem g47_diff_ineq (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {x₁ x₂ z₁ z₂ : ℝ → ℝ}
    (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂)
    (h₁ : SolvesRegulator μ a x₁ z₁) (h₂ : SolvesRegulator μ a x₂ z₂) (t : ℝ) (ht : 0 ≤ t) :
    |z₂ t - z₁ t| ≤ |x₂ t - x₁ t| +
      ∫ s in Set.Icc 0 t, |z₂ (max (t - s) 0) - z₁ (max (t - s) 0)| ∂μ ∧
    Integrable (fun s => |z₂ (max (t - s) 0) - z₁ (max (t - s) 0)|) (μ.restrict (Set.Icc 0 t)) := by
  have I1 := g47_integrable_F μ hz₁ a t
  have I2 := g47_integrable_F μ hz₂ a t
  have hI : Integrable (fun s => |z₂ (max (t - s) 0) - z₁ (max (t - s) 0)|)
      (μ.restrict (Set.Icc 0 t)) := by
    obtain ⟨M1, hM1⟩ := g47_cadlag_bdd hz₁ t
    obtain ⟨M2, hM2⟩ := g47_cadlag_bdd hz₂ t
    refine Integrable.of_bound
      (((g47_comp_meas hz₂ t).sub (g47_comp_meas hz₁ t)).abs.aestronglyMeasurable) (M2 + M1) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
    have hm : max (t - s) 0 ∈ Set.Icc 0 t := ⟨le_max_right _ _, by
      rw [max_le_iff]; exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩⟩
    rw [Real.norm_eq_abs, abs_abs]
    have := abs_sub (z₂ (max (t - s) 0)) (z₁ (max (t - s) 0))
    linarith [hM1 _ hm, hM2 _ hm]
  refine ⟨?_, hI⟩
  rw [h₁ t ht, h₂ t ht, g47_integrand_eq z₁, g47_integrand_eq z₂]
  have e : (∫ s in Set.Icc 0 t, max (z₂ (max (t - s) 0) + a) 0 ∂μ) -
      ∫ s in Set.Icc 0 t, max (z₁ (max (t - s) 0) + a) 0 ∂μ =
      ∫ s in Set.Icc 0 t, (max (z₂ (max (t - s) 0) + a) 0 - max (z₁ (max (t - s) 0) + a) 0) ∂μ :=
    (integral_sub I2 I1).symm
  have hb : |∫ s in Set.Icc 0 t, (max (z₂ (max (t - s) 0) + a) 0 - max (z₁ (max (t - s) 0) + a) 0) ∂μ|
      ≤ ∫ s in Set.Icc 0 t, |z₂ (max (t - s) 0) - z₁ (max (t - s) 0)| ∂μ := by
    refine (abs_integral_le_integral_abs).trans (integral_mono (I2.sub I1).abs hI (fun s => ?_))
    have := abs_max_sub_max_le_abs (z₂ (max (t - s) 0) + a) (z₁ (max (t - s) 0) + a) 0
    rw [add_sub_add_right_eq_sub] at this
    exact this
  have h3 := abs_add_le (x₂ t - x₁ t) ((∫ s in Set.Icc 0 t, max (z₂ (max (t - s) 0) + a) 0 ∂μ) -
      ∫ s in Set.Icc 0 t, max (z₁ (max (t - s) 0) + a) 0 ∂μ)
  rw [e] at h3
  rw [(show x₂ t + (∫ s in Set.Icc 0 t, max (z₂ (max (t - s) 0) + a) 0 ∂μ) -
      (x₁ t + ∫ s in Set.Icc 0 t, max (z₁ (max (t - s) 0) + a) 0 ∂μ) =
      x₂ t - x₁ t + ((∫ s in Set.Icc 0 t, max (z₂ (max (t - s) 0) + a) 0 ∂μ) -
      ∫ s in Set.Icc 0 t, max (z₁ (max (t - s) 0) + a) 0 ∂μ) by ring), e]
  linarith


theorem g47_integral_dirac_Icc (c t : ℝ) (f : ℝ → ℝ) :
    ∫ s in Set.Icc 0 t, f s ∂(Measure.dirac c) = if c ∈ Set.Icc 0 t then f c else 0 := by
  classical
  rw [restrict_dirac' measurableSet_Icc]
  split_ifs <;> simp [integral_dirac]

theorem g47_pml_core (c a : ℝ) (hc : 0 < c) (x₁ x₂ z₁ z₂ : ℝ → ℝ)
    (hx₁ : IsCadlag x₁) (hx₂ : IsCadlag x₂)
    (h₁ : SolvesRegulator (Measure.dirac c) a x₁ z₁)
    (h₂ : SolvesRegulator (Measure.dirac c) a x₂ z₂) :
    (∀ t : ℝ, 0 ≤ t → t < c → supNorm t (z₁ - z₂) = supNorm t (x₁ - x₂)) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, ((k : ℝ) - 1) * c ≤ t → t < k * c →
      supNorm t (z₁ - z₂) ≤ k * supNorm t (x₁ - x₂) := by
  have e1 : ∀ t, 0 ≤ t → t < c → z₁ t = x₁ t := fun t ht htc => by
    rw [h₁ t ht, g47_integral_dirac_Icc, if_neg (fun h => by linarith [h.2])]; ring
  have e2 : ∀ t, 0 ≤ t → t < c → z₂ t = x₂ t := fun t ht htc => by
    rw [h₂ t ht, g47_integral_dirac_Icc, if_neg (fun h => by linarith [h.2])]; ring
  have f1 : ∀ t, c ≤ t → z₁ t = x₁ t + max (z₁ (t - c) + a) 0 := fun t ht => by
    rw [h₁ t (by linarith), g47_integral_dirac_Icc, if_pos ⟨hc.le, ht⟩]
  have f2 : ∀ t, c ≤ t → z₂ t = x₂ t + max (z₂ (t - c) + a) 0 := fun t ht => by
    rw [h₂ t (by linarith), g47_integral_dirac_Icc, if_pos ⟨hc.le, ht⟩]
  constructor
  · intro t ht htc
    unfold supNorm
    refine iSup_congr fun s => ?_
    simp only [Pi.sub_apply]
    rw [e1 s s.2.1 (by linarith [s.2.2]), e2 s s.2.1 (by linarith [s.2.2])]
  · intro k hk t ht1 ht2
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have ht0 : 0 ≤ t := le_trans (mul_nonneg (by linarith) hc.le) ht1
    obtain ⟨M, hM⟩ := g47_sub_bdd hx₂ hx₁ t
    have hD : ∀ s ∈ Set.Icc 0 t, |x₁ s - x₂ s| ≤ supNorm t (x₁ - x₂) := fun s hs =>
      g47_le_supNorm (f := x₁ - x₂) hM hs
    have hD0 : 0 ≤ supNorm t (x₁ - x₂) := g47_supNorm_nonneg _ _
    have key : ∀ m : ℕ, ∀ s, 0 ≤ s → s ≤ t → s < (m+1) * c →
        |z₁ s - z₂ s| ≤ (m+1) * supNorm t (x₁ - x₂) := by
      intro m
      induction m with
      | zero =>
        intro s hs0 hst hsc
        simp only [Nat.cast_zero, zero_add, one_mul] at hsc
        rw [e1 s hs0 hsc, e2 s hs0 hsc]
        have := hD s ⟨hs0, hst⟩
        simp only [Nat.cast_zero, zero_add, one_mul]; exact this
      | succ m ih =>
        intro s hs0 hst hsc
        push_cast at hsc ⊢
        rcases lt_or_ge s c with hsc' | hsc'
        · rw [e1 s hs0 hsc', e2 s hs0 hsc']
          have := hD s ⟨hs0, hst⟩
          have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
          nlinarith
        · rw [f1 s hsc', f2 s hsc']
          have h1 := ih (s - c) (by linarith) (by linarith) (by linarith)
          have h2 := hD s ⟨hs0, hst⟩
          have h3 := abs_max_sub_max_le_abs (z₁ (s - c) + a) (z₂ (s - c) + a) 0
          rw [add_sub_add_right_eq_sub] at h3
          have h4 := abs_add_le (x₁ s - x₂ s)
            (max (z₁ (s - c) + a) 0 - max (z₂ (s - c) + a) 0)
          rw [show x₁ s - x₂ s + (max (z₁ (s - c) + a) 0 - max (z₂ (s - c) + a) 0) =
            x₁ s + max (z₁ (s - c) + a) 0 - (x₂ s + max (z₂ (s - c) + a) 0) by ring] at h4
          linarith
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    refine g47_supNorm_le ht0 (fun s hs => ?_)
    simp only [Pi.sub_apply]
    have := key m s hs.1 hs.2 (by push_cast at ht2; linarith [hs.2])
    push_cast; exact this

theorem g47_uniq_gen (μ : Measure ℝ) [IsFiniteMeasure μ] (δ ε : ℝ) (hδ : 0 < δ) (hε₁ : ε < 1)
    (hB₀ : μ.real (Set.Icc 0 δ) ≤ ε) (e : ℝ → ℝ) (he0 : ∀ r, 0 ≤ e r)
    (hbdd : ∀ T, ∃ M, ∀ s ∈ Set.Icc 0 T, |e s| ≤ M)
    (hineq : ∀ t, 0 ≤ t → e t ≤ ∫ s in Set.Icc 0 t, e (t - s) ∂μ)
    (hint : ∀ t, 0 ≤ t → Integrable (fun s => e (t - s)) (μ.restrict (Set.Icc 0 t))) :
    ∀ t, 0 ≤ t → e t = 0 := by
  have P : ∀ k : ℕ, ∀ r, 0 ≤ r → r < k * δ → e r = 0 := by
    intro k
    induction k with
    | zero => intro r hr hr2; simp at hr2; linarith
    | succ k ih =>
      have hT : (0:ℝ) ≤ (k+1:ℕ) * δ := by positivity
      obtain ⟨M, hM⟩ := hbdd ((k+1:ℕ) * δ)
      set Z := supNorm ((k+1:ℕ) * δ) e with hZ
      have hZ0 : 0 ≤ Z := g47_supNorm_nonneg _ _
      have hle : ∀ t ∈ Set.Icc 0 ((k+1:ℕ) * δ), e t ≤ ε * Z := by
        intro t ht
        refine (hineq t ht.1).trans ?_
        have hmono : ∫ s in Set.Icc 0 t, e (t - s) ∂μ ≤
            ∫ s in Set.Icc 0 t, (Set.Icc 0 δ).indicator (fun _ => Z) s ∂μ := by
          refine setIntegral_mono_on (hint t ht.1) ((integrable_const Z).indicator measurableSet_Icc)
            measurableSet_Icc (fun s hs => ?_)
          by_cases hsd : s ≤ δ
          · rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 δ from ⟨hs.1, hsd⟩)]
            have := g47_le_supNorm (s := t - s) hM (show t - s ∈ Set.Icc 0 _ from ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩)
            rwa [abs_of_nonneg (he0 _)] at this
          · rw [Set.indicator_of_notMem (fun h => hsd h.2)]
            push_cast at ht
            rw [ih (t - s) (by linarith [hs.2]) (by nlinarith [ht.2])]
        refine hmono.trans ?_
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_restrict_apply measurableSet_Icc,
          smul_eq_mul]
        have : μ.real (Set.Icc 0 δ ∩ Set.Icc 0 t) ≤ ε :=
          (measureReal_mono Set.inter_subset_left).trans hB₀
        nlinarith
      have hZle : Z ≤ ε * Z := g47_supNorm_le hT (fun t ht => by
        rw [abs_of_nonneg (he0 _)]; exact hle t ht)
      have hZ00 : Z = 0 := by nlinarith
      intro r hr hr2
      have := g47_le_supNorm (s := r) hM (show r ∈ Set.Icc 0 _ from ⟨hr, hr2.le⟩)
      rw [← hZ, hZ00, abs_of_nonneg (he0 _)] at this
      exact le_antisymm this (he0 r)
  intro t ht
  obtain ⟨k, hk⟩ := exists_nat_gt (t / δ)
  exact P k t ht (by rwa [div_lt_iff₀ hδ] at hk)

theorem g47_e_bdd {z₁ z₂ : ℝ → ℝ} (hz₁ : IsCadlag z₁) (hz₂ : IsCadlag z₂) (T : ℝ) :
    ∃ M, ∀ s ∈ Set.Icc 0 T, |(fun r => |z₂ (max r 0) - z₁ (max r 0)|) s| ≤ M := by
  obtain ⟨M, hM⟩ := g47_sub_bdd hz₁ hz₂ T
  refine ⟨M, fun s hs => ?_⟩
  simp only [abs_abs]
  rw [max_eq_left hs.1]
  exact hM s hs

theorem g47_uniq_of (μ : Measure ℝ) [IsFiniteMeasure μ] (a δ ε : ℝ) (hδ : 0 < δ) (hε₁ : ε < 1)
    (hB₀ : μ.real (Set.Icc 0 δ) ≤ ε)
    (x u v : ℝ → ℝ) (hu : IsCadlag u) (hv : IsCadlag v)
    (hsu : SolvesRegulator μ a x u) (hsv : SolvesRegulator μ a x v) :
    Set.EqOn u v (Set.Ici 0) := by
  have := g47_uniq_gen μ δ ε hδ hε₁ hB₀ (fun r => |v (max r 0) - u (max r 0)|)
    (fun r => abs_nonneg _) (g47_e_bdd hu hv)
    (fun t ht => by
      have h := (g47_diff_ineq μ a hu hv hsu hsv t ht).1
      rw [max_eq_left ht]; simpa using h)
    (fun t ht => (g47_diff_ineq μ a hu hv hsu hsv t ht).2)
  intro t ht
  have h := this t ht
  simp only [max_eq_left (show (0:ℝ) ≤ t from ht), abs_eq_zero, sub_eq_zero] at h
  exact h.symm

theorem g47_uniqueness_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (x u v : ℝ → ℝ) (hu : IsCadlag u) (hv : IsCadlag v)
    (hsu : SolvesRegulator μ a x u) (hsv : SolvesRegulator μ a x v) :
    Set.EqOn u v (Set.Ici 0) :=
  g47_uniq_of μ a δ ε hδ hε₁ (ENNReal.toReal_lt_of_lt_ofReal hB₀).le x u v hu hv hsu hsv


theorem g47_cadlag_approx {x : ℝ → ℝ} (hx : IsCadlag x) (s : ℝ) :
    Tendsto (fun n : ℕ => x (max ((⌈s * 2^n⌉ : ℝ) / 2^n) 0)) atTop (𝓝 (x (max s 0))) := by
  rcases le_or_gt 0 s with hs | hs
  · rw [max_eq_left hs]
    have h1 := (hx.1 s hs).tendsto.comp (g47_q_tendsto s)
    refine h1.congr' ?_
    filter_upwards with n
    simp only [Function.comp]
    rw [max_eq_left (hs.trans (g47_q_bounds s n).1)]
  · rw [max_eq_right hs.le]
    have : ∀ᶠ n in atTop, (⌈s * 2^n⌉ : ℝ) / 2^n < 0 := by
      have h := (tendsto_order.1 g47_tendsto_inv_pow).2 (-s) (by linarith)
      filter_upwards [h] with n hn
      linarith [(g47_q_bounds s n).2]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [this] with n hn
    rw [max_eq_right hn.le]

theorem g47_eval_meas (c : ℝ) (hc : 0 ≤ c) : Measurable (fun u : Dpath => u.path c) :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun t (_ : t ∈ Set.Ici (0:ℝ)) =>
    MeasurableSpace.comap (fun x : Dpath => x.path t) inferInstance) c hc)

theorem g47_joint_meas : Measurable (fun p : Dpath × ℝ => p.1.path (max p.2 0)) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n p => p.1.path (max ((⌈p.2 * 2^n⌉ : ℝ) / 2^n) 0)) ?_ ?_
  · intro n
    have : (fun p : Dpath × ℝ => p.1.path (max ((⌈p.2 * 2^n⌉ : ℝ) / 2^n) 0)) =
        (fun q : Dpath × ℤ => q.1.path (max ((q.2:ℝ) / 2^n) 0)) ∘
          (fun p : Dpath × ℝ => (p.1, ⌈p.2 * 2^n⌉)) := rfl
    rw [this]
    refine Measurable.comp ?_ (measurable_fst.prodMk
      (Int.measurable_ceil.comp (measurable_snd.mul_const _)))
    exact measurable_from_prod_countable_left fun k => g47_eval_meas (max ((k:ℝ) / 2^n) 0) (le_max_right _ _)
  · rw [tendsto_pi_nhds]; intro p
    exact g47_cadlag_approx p.1.cadlag p.2

theorem g47_psi_meas_core (μ : Measure ℝ) [IsFiniteMeasure μ] (a t : ℝ) :
    Measurable (fun u : Dpath => psi μ a u.path t) := by
  have hF : Measurable (fun p : Dpath × ℝ => max (p.1.path (max (t - p.2) 0) + a) 0) :=
    ((g47_joint_meas.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))).add_const
      a).max measurable_const
  have h2 := (StronglyMeasurable.integral_prod_right (ν := μ.restrict (Set.Icc 0 t))
    (f := fun (u : Dpath) (s : ℝ) => max (u.path (max (t - s) 0) + a) 0)
    hF.stronglyMeasurable).measurable
  have e : (fun u : Dpath => psi μ a u.path t) =
      fun u : Dpath => ∫ s in Set.Icc 0 t, max (u.path (max (t - s) 0) + a) 0 ∂μ :=
    funext fun u => g47_integrand_eq u.path a t μ
  rw [e]; exact h2

theorem g47_psi_eq (μ : Measure ℝ) (a : ℝ) (u : ℝ → ℝ) (t : ℝ) :
    psi μ a u t = ∫ s, (Set.Icc 0 t).indicator (fun s => max (u (max (t - s) 0) + a) 0) s ∂μ := by
  rw [integral_indicator measurableSet_Icc, psi, g47_integrand_eq]

theorem g47_psi_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {u : ℝ → ℝ}
    (hu : IsCadlag u) (l : Filter ℝ) [l.IsCountablyGenerated] (C : ℝ) (g : ℝ → ℝ)
    (hb : ∀ᶠ t' in l, ∀ s, |(Set.Icc 0 t').indicator (fun s => max (u (max (t' - s) 0) + a) 0) s| ≤ C)
    (hlim : ∀ s, Tendsto (fun t' => (Set.Icc 0 t').indicator
      (fun s => max (u (max (t' - s) 0) + a) 0) s) l (𝓝 (g s))) :
    Tendsto (fun t' => psi μ a u t') l (𝓝 (∫ s, g s ∂μ)) := by
  simp only [g47_psi_eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
    (integrable_const C) (Eventually.of_forall hlim)
  · exact Eventually.of_forall fun t' =>
      ((((g47_comp_meas hu t').add_const a).max measurable_const).indicator
        measurableSet_Icc).aestronglyMeasurable
  · exact hb.mono fun t' h => Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact h s

theorem g47_ind_bound {u : ℝ → ℝ} (a T M : ℝ) (hM : ∀ s ∈ Set.Icc 0 T, |u s| ≤ M) (t' : ℝ)
    (ht' : t' ≤ T) (s : ℝ) :
    |(Set.Icc 0 t').indicator (fun s => max (u (max (t' - s) 0) + a) 0) s| ≤ |M| + |a| := by
  by_cases hs : s ∈ Set.Icc 0 t'
  · rw [Set.indicator_of_mem hs]
    have h1 := hM (max (t' - s) 0) ⟨le_max_right _ _, by
      rw [max_le_iff]; exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩⟩
    have h2 : |max (u (max (t' - s) 0) + a) 0| ≤ |u (max (t' - s) 0) + a| := by
      have := abs_max_sub_max_le_abs (u (max (t' - s) 0) + a) 0 0
      simpa using this
    have h3 := abs_add_le (u (max (t' - s) 0)) a
    have h4 := le_abs_self M
    linarith
  · rw [Set.indicator_of_notMem hs, abs_zero]; positivity

theorem g47_psi_cadlag_core (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) (u : ℝ → ℝ)
    (hu : IsCadlag u) : IsCadlag (psi μ a u) := by
  constructor
  · intro t ht
    obtain ⟨M, hM⟩ := g47_cadlag_bdd hu (t + 1)
    have := g47_psi_tendsto μ a hu (𝓝[≥] t) (|M| + |a|)
      ((Set.Icc 0 t).indicator (fun s => max (u (max (t - s) 0) + a) 0)) ?_ ?_
    · rw [← g47_psi_eq μ a u t] at this
      exact this
    · have : ∀ᶠ t' in 𝓝[≥] t, t' < t + 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
      filter_upwards [this] with t' ht'
      exact g47_ind_bound a (t + 1) M hM t' ht'.le
    · intro s
      by_cases hs0 : s < 0
      · have : ∀ t', (Set.Icc 0 t').indicator (fun s => max (u (max (t' - s) 0) + a) 0) s = 0 :=
          fun t' => Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        simp only [this]; exact tendsto_const_nhds
      push_neg at hs0
      by_cases hst : t < s
      · rw [Set.indicator_of_notMem (fun h => by linarith [h.2])]
        have : ∀ᶠ t' in 𝓝[≥] t, t' < s := nhdsWithin_le_nhds (Iio_mem_nhds hst)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [this] with t' ht'
        rw [Set.indicator_of_notMem (fun h => by linarith [h.2])]
      push_neg at hst
      rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 t from ⟨hs0, hst⟩), max_eq_left (show (0:ℝ) ≤ t - s by linarith)]
      have h1 : Tendsto (fun t' => t' - s) (𝓝[≥] t) (𝓝[≥] (t - s)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact ((continuous_id.sub continuous_const).tendsto t).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t' ht'
          simp only [Set.mem_Ici] at ht' ⊢; linarith
      have h2 := (((hu.1 (t - s) (by linarith)).tendsto.comp h1).add_const a).max
        (tendsto_const_nhds (x := (0:ℝ)))
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t' ht'
      simp only [Set.mem_Ici] at ht'
      rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 t' from ⟨hs0, by linarith⟩),
        max_eq_left (show (0:ℝ) ≤ t' - s by linarith)]
      rfl
  · intro t ht
    obtain ⟨M, hM⟩ := g47_cadlag_bdd hu t
    let ul : ℝ → ℝ := fun r => limUnder (𝓝[<] r) u
    refine ⟨_, g47_psi_tendsto μ a hu (𝓝[<] t) (|M| + |a|)
      ((Set.Ico 0 t).indicator (fun s => max (ul (t - s) + a) 0)) ?_ ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with t' ht'
      exact g47_ind_bound a t M hM t' (le_of_lt ht')
    · intro s
      by_cases hs0 : s < 0
      · rw [Set.indicator_of_notMem (fun h => by linarith [h.1])]
        have : ∀ t', (Set.Icc 0 t').indicator (fun s => max (u (max (t' - s) 0) + a) 0) s = 0 :=
          fun t' => Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        simp only [this]; exact tendsto_const_nhds
      push_neg at hs0
      by_cases hst : t ≤ s
      · rw [Set.indicator_of_notMem (fun h => by linarith [h.2])]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t' ht'
        simp only [Set.mem_Iio] at ht'
        rw [Set.indicator_of_notMem (fun h => by linarith [h.2])]
      push_neg at hst
      rw [Set.indicator_of_mem (show s ∈ Set.Ico 0 t from ⟨hs0, hst⟩)]
      have h1 : Tendsto (fun t' => t' - s) (𝓝[<] t) (𝓝[<] (t - s)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · exact ((continuous_id.sub continuous_const).tendsto t).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t' ht'
          simp only [Set.mem_Iio] at ht' ⊢; linarith
      have hl : Tendsto u (𝓝[<] (t - s)) (𝓝 (ul (t - s))) :=
        tendsto_nhds_limUnder (hu.2 (t - s) (by linarith))
      have h2 := ((hl.comp h1).add_const a).max (tendsto_const_nhds (x := (0:ℝ)))
      refine h2.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hst] with t' ht'
      rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 t' from ⟨hs0, ht'.1.le⟩),
        max_eq_left (show (0:ℝ) ≤ t' - s by linarith [ht'.1])]
      rfl


theorem g47_const_cadlag (c : ℝ) : IsCadlag (fun _ => c) :=
  ⟨fun _ _ => continuousWithinAt_const, fun _ _ => ⟨c, tendsto_const_nhds⟩⟩

theorem g47_cadlag_add {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun t => f t + g t) :=
  ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht), fun t ht => by
    obtain ⟨l1, h1⟩ := hf.2 t ht
    obtain ⟨l2, h2⟩ := hg.2 t ht
    exact ⟨l1 + l2, h1.add h2⟩⟩

theorem g47_picard_cadlag (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {x : ℝ → ℝ}
    (hx : IsCadlag x) (n : ℕ) : IsCadlag (picard μ a x n) := by
  induction n with
  | zero => exact g47_const_cadlag 0
  | succ n ih =>
    show IsCadlag (fun t => x t + psi μ a (picard μ a x n) t)
    exact g47_cadlag_add hx (g47_psi_cadlag_core μ a _ ih)

theorem g47_psi_diff (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ) {u v : ℝ → ℝ}
    (hu : IsCadlag u) (hv : IsCadlag v) (t : ℝ) :
    |psi μ a v t - psi μ a u t| ≤
      ∫ s in Set.Icc 0 t, |v (max (t - s) 0) - u (max (t - s) 0)| ∂μ ∧
    Integrable (fun s => |v (max (t - s) 0) - u (max (t - s) 0)|) (μ.restrict (Set.Icc 0 t)) := by
  have I1 := g47_integrable_F μ hu a t
  have I2 := g47_integrable_F μ hv a t
  have hI : Integrable (fun s => |v (max (t - s) 0) - u (max (t - s) 0)|)
      (μ.restrict (Set.Icc 0 t)) := by
    obtain ⟨M1, hM1⟩ := g47_cadlag_bdd hu t
    obtain ⟨M2, hM2⟩ := g47_cadlag_bdd hv t
    refine Integrable.of_bound
      (((g47_comp_meas hv t).sub (g47_comp_meas hu t)).abs.aestronglyMeasurable) (M2 + M1) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
    have hm : max (t - s) 0 ∈ Set.Icc 0 t := ⟨le_max_right _ _, by
      rw [max_le_iff]; exact ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩⟩
    rw [Real.norm_eq_abs, abs_abs]
    have := abs_sub (v (max (t - s) 0)) (u (max (t - s) 0))
    linarith [hM1 _ hm, hM2 _ hm]
  refine ⟨?_, hI⟩
  unfold psi
  rw [g47_integrand_eq u, g47_integrand_eq v, ← integral_sub I2 I1]
  refine (abs_integral_le_integral_abs).trans (integral_mono (I2.sub I1).abs hI (fun s => ?_))
  have := abs_max_sub_max_le_abs (v (max (t - s) 0) + a) (u (max (t - s) 0) + a) 0
  rw [add_sub_add_right_eq_sub] at this
  exact this

theorem g47_kernel (μ : Measure ℝ) [IsFiniteMeasure μ] (δ ε : ℝ) (hδ : 0 < δ) (hε₀ : 0 < ε)
    (hε₁ : ε < 1)
    (hB0r : μ.real (Set.Icc 0 δ) < ε) (hBr : ∀ y, 0 ≤ y → μ.real (Set.Ioc y (y + δ)) < ε) :
    ∃ β c : ℝ, 0 ≤ β ∧ 0 ≤ c ∧ c < 1 ∧
      ∀ t, 0 ≤ t → ∫ s in Set.Icc 0 t, Real.exp (-β * s) ∂μ ≤ c := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 - ε) / 2 := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; linarith
  have hq1 : q < 1 := by rw [hq]; linarith
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -Real.log q / δ := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by rw [hβ]; exact div_nonneg (by linarith) hδ.le
  have hexp : ∀ k : ℕ, Real.exp (-β * (k * δ)) = q ^ k := by
    intro k
    have : -β * (k * δ) = k * Real.log q := by rw [hβ]; field_simp
    rw [this, Real.exp_nat_mul, Real.exp_log hq0]
  refine ⟨β, ε / (1 - q), hβ0, div_nonneg hε₀.le (by linarith),
    (div_lt_one (by linarith)).2 (by rw [hq]; linarith), fun t ht => ?_⟩
  set N := ⌈t / δ⌉₊ with hN
  have hcont : Continuous (fun s : ℝ => Real.exp (-β * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hqpow : ∀ i : ℕ, 0 ≤ q ^ i := fun i => pow_nonneg hq0.le i
  have hmono : ∫ s in Set.Icc 0 t, Real.exp (-β * s) ∂μ ≤
      ∫ s in Set.Icc 0 t, ((Set.Icc 0 δ).indicator (fun _ => (1:ℝ)) s +
        ∑ i ∈ Finset.range N, (Set.Ioc (((i:ℝ)+1) * δ) (((i:ℝ)+1) * δ + δ)).indicator
          (fun _ => q ^ (i + 1)) s) ∂μ := by
    refine setIntegral_mono_on hcont.integrableOn_Icc
      (((integrable_const _).indicator measurableSet_Icc).add
        (integrable_finset_sum _ (fun i _ => (integrable_const _).indicator measurableSet_Ioc)))
      measurableSet_Icc (fun s hs => ?_)
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, (Set.Ioc (((i:ℝ)+1) * δ) (((i:ℝ)+1) * δ + δ)).indicator
          (fun _ => q ^ (i + 1)) s :=
      Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => hqpow _) _
    by_cases hsd : s ≤ δ
    · rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 δ from ⟨hs.1, hsd⟩)]
      have : Real.exp (-β * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hs.1])
      linarith
    · push_neg at hsd
      have h0 : 0 ≤ (Set.Icc 0 δ).indicator (fun _ => (1:ℝ)) s :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have hk1 : s / δ ≤ ((⌈s / δ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have hk2 : ((⌈s / δ⌉₊ : ℕ) : ℝ) < s / δ + 1 := Nat.ceil_lt_add_one (div_nonneg hs.1 hδ.le)
      have hkN : ⌈s / δ⌉₊ ≤ N := Nat.ceil_mono (div_le_div_of_nonneg_right hs.2 hδ.le)
      have hsd' : 1 < s / δ := by rw [lt_div_iff₀ hδ]; linarith
      have hk3 : 2 ≤ ⌈s / δ⌉₊ := by
        have : (1:ℝ) < ((⌈s / δ⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hsd' hk1
        exact_mod_cast this
      generalize ⌈s / δ⌉₊ = k at hk1 hk2 hkN hk3
      obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
      push_cast at hk1 hk2
      have hs1 : ((i:ℝ) + 1) * δ < s := by
        have : (i:ℝ) + 1 < s / δ := by linarith
        rwa [lt_div_iff₀ hδ] at this
      have hs2 : s ≤ ((i:ℝ) + 1) * δ + δ := by
        have : s ≤ ((i:ℝ) + 2) * δ := by rwa [div_le_iff₀ hδ] at hk1
        linarith
      have hmem : s ∈ Set.Ioc (((i:ℝ)+1) * δ) (((i:ℝ)+1) * δ + δ) := ⟨hs1, hs2⟩
      have hle : (Set.Ioc (((i:ℝ)+1) * δ) (((i:ℝ)+1) * δ + δ)).indicator
          (fun _ => q ^ (i + 1)) s ≤ ∑ i ∈ Finset.range N, (Set.Ioc (((i:ℝ)+1) * δ)
            (((i:ℝ)+1) * δ + δ)).indicator (fun _ => q ^ (i + 1)) s :=
        Finset.single_le_sum (f := fun i : ℕ => (Set.Ioc (((i:ℝ)+1) * δ)
            (((i:ℝ)+1) * δ + δ)).indicator (fun _ => q ^ (i + 1)) s)
          (fun k _ => Set.indicator_nonneg (fun _ _ => hqpow (k + 1)) _)
          (Finset.mem_range.2 (by omega))
      rw [Set.indicator_of_mem hmem] at hle
      have he : Real.exp (-β * s) ≤ q ^ (i + 1) := by
        rw [← hexp (i + 1)]
        apply Real.exp_le_exp.2
        push_cast
        nlinarith
      linarith
  refine hmono.trans ?_
  rw [integral_add ((integrable_const _).indicator measurableSet_Icc)
    (integrable_finset_sum _ (fun i _ => (integrable_const _).indicator measurableSet_Ioc)),
    integral_finset_sum _ (fun i _ => (integrable_const _).indicator measurableSet_Ioc)]
  simp only [integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Ioc, smul_eq_mul]
  have h1 : μ.real (Set.Icc 0 δ ∩ Set.Icc 0 t) * 1 ≤ ε := by
    rw [mul_one]; exact (measureReal_mono Set.inter_subset_left).trans hB0r.le
  have h2 : ∑ i ∈ Finset.range N, μ.real (Set.Ioc (((i:ℝ)+1) * δ) (((i:ℝ)+1) * δ + δ) ∩
      Set.Icc 0 t) * q ^ (i + 1) ≤ ∑ i ∈ Finset.range N, ε * q ^ (i + 1) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
      ((measureReal_mono Set.inter_subset_left).trans (hBr _ (by positivity)).le) (hqpow _)
  have h3 : ∑ i ∈ Finset.range N, ε * q ^ (i + 1) ≤ ε * (q / (1 - q)) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hε₀.le
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0.le hq1
    rw [← Finset.range_eq_Ico, pow_zero] at this
    have e : ∑ i ∈ Finset.range N, q ^ (i + 1) = q * ∑ i ∈ Finset.range N, q ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_succ' q i
    rw [e]
    calc q * ∑ i ∈ Finset.range N, q ^ i ≤ q * (1 / (1 - q)) :=
          mul_le_mul_of_nonneg_left this hq0.le
      _ = q / (1 - q) := by ring
  have h4 : ε + ε * (q / (1 - q)) = ε / (1 - q) := by
    have : (1 - q) ≠ 0 := by linarith
    field_simp; ring
  linarith


theorem g47_unif_cadlag (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (hF : ∀ n, IsCadlag (F n))
    (hu : ∀ T, 0 ≤ T → ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ n, ∀ t ∈ Set.Icc 0 T, |F n t - f t| ≤ g n) : IsCadlag f := by
  have hTU : ∀ T, 0 ≤ T → ∀ l' : Filter ℝ, (∀ᶠ y in l', y ∈ Set.Icc 0 T) →
      TendstoUniformlyOnFilter F f atTop l' := by
    intro T hT l' hl'
    obtain ⟨g, hg0, hg⟩ := hu T hT
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro η hη
    have h1 : ∀ᶠ n in atTop, g n < η := (tendsto_order.1 hg0).2 η hη
    filter_upwards [h1.prod_mk hl'] with q hq
    rw [dist_comm, Real.dist_eq]; exact (hg q.1 q.2 hq.2).trans_lt hq.1
  constructor
  · intro t ht
    have hU := hTU (t+1) (by linarith) (𝓝[≥] t) (by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with y hy1 hy2
      exact ⟨ht.trans hy1, le_of_lt hy2⟩)
    obtain ⟨g, hg0, hg⟩ := hu t ht
    have hL : Tendsto (fun n => F n t) atTop (𝓝 (f t)) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
        (fun n => by rw [Real.dist_eq]; exact hg n t ⟨ht, le_rfl⟩) hg0)
    exact hU.tendsto_of_eventually_tendsto (Eventually.of_forall fun n => ((hF n).1 t ht).tendsto) hL
  · intro t ht
    have hLn : ∀ n, Tendsto (F n) (𝓝[<] t) (𝓝 (limUnder (𝓝[<] t) (F n))) := fun n =>
      tendsto_nhds_limUnder ((hF n).2 t ht)
    obtain ⟨g, hg0, hg⟩ := hu t ht.le
    have hev : ∀ᶠ y in 𝓝[<] t, y ∈ Set.Icc 0 t := by
      filter_upwards [Ioo_mem_nhdsLT ht] with y hy; exact ⟨hy.1.le, hy.2.le⟩
    have hLL : ∀ n m, |limUnder (𝓝[<] t) (F n) - limUnder (𝓝[<] t) (F m)| ≤ g n + g m := by
      intro n m
      have h := ((hLn n).sub (hLn m)).abs
      refine le_of_tendsto h ?_
      filter_upwards [hev] with y hy
      have h1 := hg n y hy
      have h2 := hg m y hy
      have := abs_sub_le (F n y) (f y) (F m y)
      rw [abs_sub_comm (f y)] at this
      linarith
    have hC : CauchySeq (fun n => limUnder (𝓝[<] t) (F n)) := by
      refine Metric.cauchySeq_iff'.2 (fun η hη => ?_)
      obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hg0).2 (η/2) (by linarith))
      refine ⟨N, fun n hn => ?_⟩
      rw [Real.dist_eq]
      have := hLL n N
      have := hN n hn
      have := hN N le_rfl
      linarith
    obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hC
    exact ⟨ℓ, (hTU t ht.le (𝓝[<] t) hev).tendsto_of_eventually_tendsto
      (Eventually.of_forall hLn) hℓ⟩

theorem g47_exist_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x : ℝ → ℝ) (hx : IsCadlag x) :
    ∃ uStar : ℝ → ℝ, IsCadlag uStar ∧
      (∀ T, 0 ≤ T → Tendsto (fun n => supNorm T (picard μ a x n - uStar)) atTop (𝓝 0)) ∧
      SolvesRegulator μ a x uStar := by
  obtain ⟨β, c, hβ, hc0, hc1, hK⟩ := g47_kernel μ δ ε hδ hε₀ hε₁
    (ENNReal.toReal_lt_of_lt_ofReal hB₀) (fun y hy => ENNReal.toReal_lt_of_lt_ofReal (hB y hy))
  have hpc : ∀ n, IsCadlag (picard μ a x n) := g47_picard_cadlag μ a hx
  have hps : ∀ n t, picard μ a x (n+1) t = x t + psi μ a (picard μ a x n) t := fun n t => rfl
  have geo : ∀ T, 0 ≤ T → ∃ A, 0 ≤ A ∧ ∀ n, ∀ t ∈ Set.Icc 0 T,
      |picard μ a x (n+1) t - picard μ a x n t| ≤ A * c ^ n := by
    intro T hT
    have hbd : ∀ n, ∃ M, ∀ t ∈ Set.Icc 0 T,
        |(fun t => Real.exp (-β * t) * (picard μ a x (n+1) t - picard μ a x n t)) t| ≤ M := by
      intro n
      obtain ⟨M, hM⟩ := g47_sub_bdd (hpc n) (hpc (n+1)) T
      refine ⟨M, fun t ht => ?_⟩
      have h1 : Real.exp (-β * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
      have h2 := hM t ht
      simp only [Pi.sub_apply] at h2
      show |Real.exp (-β * t) * (picard μ a x (n+1) t - picard μ a x n t)| ≤ M
      rw [abs_mul, Real.abs_exp]
      have := abs_nonneg (picard μ a x (n+1) t - picard μ a x n t)
      nlinarith [Real.exp_pos (-β * t)]
    have hN0 : ∀ n, 0 ≤ supNorm T (fun t => Real.exp (-β * t) *
        (picard μ a x (n+1) t - picard μ a x n t)) := fun n => g47_supNorm_nonneg _ _
    have hee : ∀ r : ℝ, Real.exp (β * r) * Real.exp (-β * r) = 1 := fun r => by
      rw [← Real.exp_add]; simp
    have hpt : ∀ n, ∀ r ∈ Set.Icc 0 T, |picard μ a x (n+1) r - picard μ a x n r| ≤
        Real.exp (β * r) * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1) t - picard μ a x n t)) := by
      intro n r hr
      have h : |Real.exp (-β * r) * (picard μ a x (n+1) r - picard μ a x n r)| ≤ _ :=
        g47_le_supNorm (hbd n).choose_spec hr
      rw [abs_mul, Real.abs_exp] at h
      calc |picard μ a x (n+1) r - picard μ a x n r| =
          Real.exp (β * r) * (Real.exp (-β * r) * |picard μ a x (n+1) r - picard μ a x n r|) := by
            rw [← mul_assoc, hee, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    have hstep : ∀ n, supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1+1) t - picard μ a x (n+1) t)) ≤
        c * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1) t - picard μ a x n t)) := by
      intro n
      set Nn := supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1) t - picard μ a x n t)) with hNn
      refine g47_supNorm_le hT (fun t ht => ?_)
      show |Real.exp (-β * t) * (picard μ a x (n+1+1) t - picard μ a x (n+1) t)| ≤ c * Nn
      rw [abs_mul, Real.abs_exp, hps (n+1) t, hps n t, add_sub_add_left_eq_sub]
      obtain ⟨h1, hint⟩ := g47_psi_diff μ a (hpc n) (hpc (n+1)) t
      have h2 : ∫ s in Set.Icc 0 t, |picard μ a x (n+1) (max (t - s) 0) -
          picard μ a x n (max (t - s) 0)| ∂μ ≤
          ∫ s in Set.Icc 0 t, (Nn * Real.exp (β * t)) * Real.exp (-β * s) ∂μ := by
        refine setIntegral_mono_on hint ?_ measurableSet_Icc (fun s hs => ?_)
        · exact (continuous_const.mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrableOn_Icc
        · rw [max_eq_left (by linarith [hs.2] : (0:ℝ) ≤ t - s)]
          have := hpt n (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
          have e : Real.exp (β * (t - s)) = Real.exp (β * t) * Real.exp (-β * s) := by
            rw [← Real.exp_add]; ring_nf
          rw [e] at this
          linarith
      rw [integral_const_mul] at h2
      have h3 := hK t ht.1
      have hpos : 0 ≤ Nn * Real.exp (β * t) := mul_nonneg (hN0 n) (Real.exp_pos _).le
      have h4 : |psi μ a (picard μ a x (n+1)) t - psi μ a (picard μ a x n) t| ≤
          Nn * Real.exp (β * t) * c := h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hpos))
      calc Real.exp (-β * t) * |psi μ a (picard μ a x (n+1)) t - psi μ a (picard μ a x n) t|
          ≤ Real.exp (-β * t) * (Nn * Real.exp (β * t) * c) :=
            mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
        _ = (Real.exp (β * t) * Real.exp (-β * t)) * (c * Nn) := by ring
        _ = c * Nn := by rw [hee, one_mul]
    have hgeo : ∀ n, supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1) t - picard μ a x n t)) ≤
        c ^ n * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (0+1) t - picard μ a x 0 t)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        refine (hstep n).trans ?_
        rw [pow_succ', mul_assoc]
        exact mul_le_mul_of_nonneg_left ih hc0
    refine ⟨Real.exp (β * T) * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (0+1) t - picard μ a x 0 t)), mul_nonneg (Real.exp_pos _).le (hN0 0),
      fun n t ht => ?_⟩
    refine (hpt n t ht).trans ?_
    have h1 : Real.exp (β * t) ≤ Real.exp (β * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hβ)
    calc Real.exp (β * t) * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (n+1) t - picard μ a x n t))
        ≤ Real.exp (β * T) * (c ^ n * supNorm T (fun t => Real.exp (-β * t) *
          (picard μ a x (0+1) t - picard μ a x 0 t))) :=
          mul_le_mul h1 (hgeo n) (hN0 n) (Real.exp_pos _).le
      _ = _ := by ring
  have hcauchy : ∀ t, 0 ≤ t → ∃ l, Tendsto (fun n => picard μ a x n t) atTop (𝓝 l) := by
    intro t ht
    obtain ⟨A, hA0, hA⟩ := geo t ht
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric c A hc1 (fun n => by
      rw [dist_comm, Real.dist_eq]; exact hA n t ⟨ht, le_rfl⟩))
  set uStar : ℝ → ℝ := fun t => limUnder atTop (fun n => picard μ a x n t) with huStar
  have hlim : ∀ t, 0 ≤ t → Tendsto (fun n => picard μ a x n t) atTop (𝓝 (uStar t)) :=
    fun t ht => tendsto_nhds_limUnder (hcauchy t ht)
  have hunif : ∀ T, 0 ≤ T → ∃ A, 0 ≤ A ∧ ∀ n, ∀ t ∈ Set.Icc 0 T,
      |picard μ a x n t - uStar t| ≤ A * c ^ n / (1 - c) := by
    intro T hT
    obtain ⟨A, hA0, hA⟩ := geo T hT
    refine ⟨A, hA0, fun n t ht => ?_⟩
    have := dist_le_of_le_geometric_of_tendsto c A hc1 (fun n => by
      rw [dist_comm, Real.dist_eq]; exact hA n t ht) (hlim t ht.1) n
    rwa [Real.dist_eq] at this
  have hg : ∀ A : ℝ, Tendsto (fun n : ℕ => A * c ^ n / (1 - c)) atTop (𝓝 0) := by
    intro A
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul A).div_const (1 - c)
    simpa using this
  have hsc : IsCadlag uStar := by
    refine g47_unif_cadlag (picard μ a x) uStar hpc (fun T hT => ?_)
    obtain ⟨A, hA0, hA⟩ := hunif T hT
    exact ⟨_, hg A, hA⟩
  refine ⟨uStar, hsc, fun T hT => ?_, fun t ht => ?_⟩
  · obtain ⟨A, hA0, hA⟩ := hunif T hT
    refine squeeze_zero (fun n => g47_supNorm_nonneg _ _)
      (fun n => g47_supNorm_le hT (fun t ht => ?_)) (hg A)
    simp only [Pi.sub_apply]; exact hA n t ht
  · have h1 : Tendsto (fun n => picard μ a x (n+1) t) atTop (𝓝 (uStar t)) :=
      (hlim t ht).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => picard μ a x (n+1) t) atTop (𝓝 (x t + psi μ a uStar t)) := by
      simp only [hps]
      refine tendsto_const_nhds.add ?_
      obtain ⟨A, hA0, hA⟩ := hunif t ht
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        (by simpa using (hg A).mul_const (μ.real (Set.Icc 0 t)))
      rw [Real.dist_eq]
      have h3 := (g47_psi_diff μ a hsc (hpc n) t).1
      have hb : ∫ s in Set.Icc 0 t, |picard μ a x n (max (t - s) 0) - uStar (max (t - s) 0)| ∂μ ≤
          A * c ^ n / (1 - c) * μ.real (Set.Icc 0 t) := by
        have := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := Set.Icc 0 t)
          (f := fun s => |picard μ a x n (max (t - s) 0) - uStar (max (t - s) 0)|)
          (C := A * c ^ n / (1 - c)) (measure_lt_top _ _) (fun s hs => by
            rw [Real.norm_eq_abs, abs_abs, max_eq_left (by linarith [hs.2] : (0:ℝ) ≤ t - s)]
            exact hA n (t - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      linarith
    exact tendsto_nhds_unique h1 h2

end ReedGGN.Regulator

open ReedGGN.Regulator
open MeasureTheory Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x : ℝ → ℝ) (hx : IsCadlag x) :
    ∃ uStar : ℝ → ℝ, IsCadlag uStar ∧
      (∀ T, 0 ≤ T → Tendsto (fun n => supNorm T (picard μ a x n - uStar)) atTop (𝓝 0)) ∧
      SolvesRegulator μ a x uStar := by
  exact g47_exist_core μ a δ ε hδ hε₀ hε₁ hB₀ hB x hx
