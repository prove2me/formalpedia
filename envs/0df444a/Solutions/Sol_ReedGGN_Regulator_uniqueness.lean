-- Prove2me | solution 1 for ReedGGN.Regulator.uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:36:33.552853+00:00
-- url     : https://prove2.me/submissions/7add680b-f58b-4166-9655-88e802521305

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

end ReedGGN.Regulator

open ReedGGN.Regulator
open MeasureTheory Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x u v : ℝ → ℝ) (hx : IsCadlag x) (hu : IsCadlag u) (hv : IsCadlag v)
    (hsu : SolvesRegulator μ a x u) (hsv : SolvesRegulator μ a x v) :
    Set.EqOn u v (Set.Ici 0) := by
  exact g47_uniqueness_core μ a δ ε hδ hε₀ hε₁ hB₀ x u v hu hv hsu hsv
