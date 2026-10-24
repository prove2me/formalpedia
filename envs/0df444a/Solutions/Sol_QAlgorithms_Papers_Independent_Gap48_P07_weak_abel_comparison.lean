-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.weak_abel_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:05:05.732075+00:00
-- url     : https://prove2.me/submissions/205ba154-37e0-4fbd-8aa9-ca743afff76b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma X7_exp_tendsto_false (a : ℝ) (ha : a ≠ 0) (c : ℂ)
    (h : Tendsto (fun r : ℝ => Complex.exp (Complex.I * (a:ℂ) * (r:ℂ))) atTop (𝓝 c)) :
    False := by
  have ha' : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have h2 : Tendsto (fun r : ℝ => Complex.exp (Complex.I * (a:ℂ) * ((r + Real.pi / a : ℝ):ℂ)))
      atTop (𝓝 c) :=
    h.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h3 : (fun r : ℝ => Complex.exp (Complex.I * (a:ℂ) * ((r + Real.pi / a : ℝ):ℂ))) =
      fun r : ℝ => - Complex.exp (Complex.I * (a:ℂ) * (r:ℂ)) := by
    funext r
    have : Complex.I * (a:ℂ) * ((r + Real.pi / a : ℝ):ℂ) =
        Complex.I * (a:ℂ) * (r:ℂ) + Real.pi * Complex.I := by
      push_cast; field_simp
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]; ring
  rw [h3] at h2
  have h4 : Tendsto (fun r : ℝ => - Complex.exp (Complex.I * (a:ℂ) * (r:ℂ))) atTop (𝓝 (-c)) :=
    h.neg
  have hc : c = -c := tendsto_nhds_unique h2 h4
  have hc0 : c = 0 := by linear_combination hc / 2
  have hn : Tendsto (fun r : ℝ => ‖Complex.exp (Complex.I * (a:ℂ) * (r:ℂ))‖) atTop (𝓝 ‖c‖) :=
    h.norm
  have h1 : (fun r : ℝ => ‖Complex.exp (Complex.I * (a:ℂ) * (r:ℂ))‖) = fun _ => (1:ℝ) := by
    funext r
    rw [Complex.norm_exp]; simp
  rw [h1, hc0, norm_zero] at hn
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

lemma X7_int_Icc (a : ℝ) (ha : a ≠ 0) (r : ℝ) (hr : 0 ≤ r) (x : X) :
    (∫ s in Icc (0:ℝ) r, Complex.exp (Complex.I * (a:ℂ) * (s:ℂ)) • x) =
      ((Complex.exp (Complex.I * (a:ℂ) * (r:ℂ)) - 1) / (Complex.I * (a:ℂ))) • x := by
  rw [integral_smul_const, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
    integral_exp_mul_complex]
  · simp
  · exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha)

lemma X7_int_Ici (a alpha : ℝ) (hal : 0 < alpha) (x : X) :
    IntegrableOn (fun s : ℝ => Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x)
      (Ici 0) ∧
    (∫ s in Ici (0 : ℝ), Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x) =
      ((alpha:ℂ) - Complex.I * a)⁻¹ • x := by
  have hre : (-(alpha : ℂ) + Complex.I * (a : ℂ)).re < 0 := by simp [hal]
  have hi : IntegrableOn (fun s : ℝ => Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)))
      (Ioi 0) := integrableOn_exp_mul_complex_Ioi hre 0
  refine ⟨?_, ?_⟩
  · exact Integrable.smul_const ((integrableOn_exp_mul_complex_Ioi hre (-1)).mono_set
      (Ici_subset_Ioi.2 (by norm_num))) x
  · rw [integral_smul_const, integral_Ici_eq_integral_Ioi, integral_exp_mul_complex_Ioi hre]
    congr 1
    have hc : (-(alpha:ℂ) + Complex.I * a) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show ((alpha:ℂ) - Complex.I * a) = -(-(alpha:ℂ) + Complex.I*a) by ring, inv_neg]
    field_simp

lemma X7_part2 (a : ℝ) (ha : a ≠ 0) (x : X) (hx : x ≠ 0) :
      (∀ alpha : ℝ, 0 < alpha → IntegrableOn
        (fun s : ℝ => Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x)
        (Ici 0)) ∧
      (∀ l : X →L[ℂ] ℂ, Tendsto
        (fun alpha : ℝ => l (∫ s in Ici (0 : ℝ),
          Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x))
        (𝓝[>] 0) (𝓝 (l ((-Complex.I * (a : ℂ))⁻¹ • x)))) ∧
      (∀ r : ℝ, 0 ≤ r → (∫ s in Icc (0 : ℝ) r,
        Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x) =
        ((Complex.exp (Complex.I * (a : ℂ) * (r : ℂ)) - 1) / (Complex.I * (a : ℂ))) • x) ∧
      ¬ ∃ y : X, ∀ l : X →L[ℂ] ℂ, Tendsto
        (fun r : ℝ => l (∫ s in Icc (0 : ℝ) r,
          Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x)) atTop (𝓝 (l y)) := by
  refine ⟨fun alpha hal => (X7_int_Ici a alpha hal x).1, ?_, fun r hr => X7_int_Icc a ha r hr x, ?_⟩
  · intro l
    have hev : (fun alpha : ℝ => l (∫ s in Ici (0 : ℝ),
          Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x)) =ᶠ[𝓝[>] 0]
        (fun alpha : ℝ => ((alpha:ℂ) - Complex.I * a)⁻¹ * l x) := by
      filter_upwards [self_mem_nhdsWithin] with alpha hal
      rw [(X7_int_Ici a alpha hal x).2, map_smul, smul_eq_mul]
    refine Tendsto.congr' hev.symm ?_
    rw [map_smul, smul_eq_mul]
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have hcont : ContinuousAt (fun alpha : ℝ => ((alpha:ℂ) - Complex.I * a)⁻¹ * l x) 0 := by
      apply ContinuousAt.mul _ continuousAt_const
      apply ContinuousAt.inv₀ (by fun_prop)
      simp [ha]
    have := hcont.tendsto
    simpa using this
  · rintro ⟨y, hy⟩
    obtain ⟨l, -, hl0⟩ := exists_dual_vector ℂ x (norm_ne_zero_iff.mpr hx)
    have hl : l x = ((‖x‖ : ℝ) : ℂ) := hl0
    have h1 := hy l
    have hxn : (‖x‖ : ℂ) ≠ 0 := by simp [hx]
    have hia : Complex.I * (a:ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ha)
    have hev : (fun r : ℝ => l (∫ s in Icc (0 : ℝ) r,
          Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x)) =ᶠ[atTop]
        (fun r : ℝ => (Complex.exp (Complex.I * (a : ℂ) * (r : ℂ)) - 1) / (Complex.I * (a : ℂ))
          * (‖x‖ : ℂ)) := by
      filter_upwards [eventually_ge_atTop 0] with r hr
      simp only [X7_int_Icc a ha r hr x, map_smul, smul_eq_mul, hl]
    have h2 := (h1.congr' hev).mul_const ((Complex.I * (a:ℂ)) / (‖x‖ : ℂ))
    have h3 := h2.add_const 1
    refine X7_exp_tendsto_false a ha _ (h3.congr' ?_)
    filter_upwards with r
    have hxn' : (‖x‖ : ℂ) ≠ 0 := hxn
    have ha' : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    field_simp
    ring

lemma X7_exp_Ici_int (c : ℝ) : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ici c) := by
  have h := exp_neg_integrableOn_Ioi (c - 1) (b := 1) one_pos
  simp only [neg_mul, one_mul] at h
  exact h.mono_set (Ici_subset_Ioi.2 (by linarith))

lemma X7_exp_Ici_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) (v : E) :
    ∫ u, (Ici c).indicator (fun u : ℝ => Real.exp (-u) • v) u = Real.exp (-c) • v := by
  rw [integral_indicator measurableSet_Ici, integral_smul_const, integral_Ici_eq_integral_Ioi,
    integral_exp_neg_Ioi]

theorem X7_part1 (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) (m : LaplaceRadon) (x y : X)
    (h : WeakImproper T m x y) : WeakAbel T m x y := by
  haveI := m.locally_finite
  obtain ⟨M, hM0, hM⟩ := hT.1.2.2.1
  have hψc : Continuous (fun s : ℝ≥0 => T (s:ℝ) x) :=
    (hT.2 x).comp_continuous NNReal.continuous_coe (fun s => (s.2 : (0:ℝ) ≤ s))
  have hψb : ∀ s : ℝ≥0, ‖T (s:ℝ) x‖ ≤ M * ‖x‖ := fun s =>
    ((T s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hM s s.2) (norm_nonneg _))
  have hph : AEStronglyMeasurable m.phase m.variation := by
    have h1 := (m.transformable 1 one_pos).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun s : ℝ≥0 => Complex.exp (((s:ℝ):ℂ))) m.variation := by
      apply Continuous.aestronglyMeasurable; fun_prop
    refine (h2.mul h1).congr (Eventually.of_forall fun s => ?_)
    show Complex.exp (((s:ℝ):ℂ)) * (Complex.exp (-((1:ℝ):ℂ) * ((s:ℝ):ℂ)) * m.phase s) = m.phase s
    rw [← mul_assoc, ← Complex.exp_add]; simp
  have hexp : ∀ a : ℝ, 0 < a → Integrable (fun s : ℝ≥0 => Real.exp (-(a * s))) m.variation := by
    intro a ha
    have h1 := (m.transformable a ha).norm
    refine h1.congr ?_
    filter_upwards [m.phase_norm] with s hs
    rw [norm_mul, hs, mul_one, Complex.norm_exp]
    congr 1; simp
  have hAbelInt : ∀ a : ℝ, 0 < a → Integrable
      (fun s : NNReal => (Complex.exp (-(a : ℂ) * ((s : ℝ) : ℂ)) * m.phase s) • T (s : ℝ) x)
      m.variation := by
    intro a ha
    exact (m.transformable a ha).smul_bdd (M * ‖x‖) hψc.aestronglyMeasurable
      (Eventually.of_forall hψb)
  refine ⟨hAbelInt, ?_⟩
  intro l
  set φ : ℝ≥0 → ℂ := fun s => l (m.phase s • T (s:ℝ) x) with hφdef
  have hφm : AEStronglyMeasurable φ m.variation :=
    l.continuous.comp_aestronglyMeasurable (hph.smul hψc.aestronglyMeasurable)
  set C : ℝ := ‖l‖ * (M * ‖x‖) with hC
  have hC0 : 0 ≤ C := by positivity
  have hφb : ∀ᵐ s ∂m.variation, ‖φ s‖ ≤ C := by
    filter_upwards [m.phase_norm] with s hs
    calc ‖φ s‖ ≤ ‖l‖ * ‖m.phase s • T (s:ℝ) x‖ := l.le_opNorm _
      _ ≤ C := by
        rw [norm_smul, hs, one_mul]; exact mul_le_mul_of_nonneg_left (hψb s) (norm_nonneg _)
  have hmeasS : ∀ r : ℝ, MeasurableSet {s : ℝ≥0 | (s:ℝ) ≤ r} := fun r =>
    measurableSet_le NNReal.continuous_coe.measurable measurable_const
  set Φ : ℝ → ℂ := fun r => ∫ s, ({s : ℝ≥0 | (s:ℝ) ≤ r}).indicator φ s ∂m.variation with hΦdef
  have hΦF : ∀ r : ℝ, 0 < r → Φ r = l (improperIntegral T m r x) := by
    intro r hr
    simp only [hΦdef, improperIntegral]
    rw [integral_indicator (hmeasS r), ← l.integral_comp_comm (h.1 r hr)]
  have hΦneg : ∀ r : ℝ, r < 0 → Φ r = 0 := by
    intro r hr
    have : ({s : ℝ≥0 | (s:ℝ) ≤ r}).indicator φ = 0 := by
      funext s; apply Set.indicator_of_notMem; simp only [mem_setOf_eq, not_le]
      exact lt_of_lt_of_le hr s.2
    simp only [hΦdef, this]; simp
  have hΦlim : Tendsto Φ atTop (𝓝 (l y)) := by
    refine (h.2 l).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    exact (hΦF r hr).symm
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ r, ‖Φ r‖ ≤ B := by
    obtain ⟨R, hR⟩ := eventually_atTop.1
      ((hΦlim.norm).eventually (gt_mem_nhds (lt_add_one ‖l y‖)))
    set R' := max R 0 with hR'
    have hset : {s : ℝ≥0 | (s:ℝ) ≤ R'} ⊆ Icc 0 (⟨R', le_max_right _ _⟩ : ℝ≥0) := by
      intro s hs; exact ⟨by positivity, NNReal.coe_le_coe.1 hs⟩
    have hfin : m.variation {s : ℝ≥0 | (s:ℝ) ≤ R'} < ⊤ :=
      (measure_mono hset).trans_lt isCompact_Icc.measure_lt_top
    refine ⟨max (‖l y‖ + 1) (C * m.variation.real {s : ℝ≥0 | (s:ℝ) ≤ R'}), ?_, fun r => ?_⟩
    · exact le_max_of_le_left (by positivity)
    by_cases hr : R ≤ r
    · exact le_max_of_le_left (hR r hr).le
    · apply le_max_of_le_right
      calc ‖Φ r‖ ≤ ∫ s, ({s : ℝ≥0 | (s:ℝ) ≤ R'}).indicator (fun _ => C) s ∂m.variation := by
            apply norm_integral_le_of_norm_le
            · exact (integrableOn_const hfin.ne).integrable_indicator (hmeasS R')
            · filter_upwards [hφb] with s hs
              by_cases h1 : (s:ℝ) ≤ r
              · have h2 : (s:ℝ) ≤ R' := h1.trans ((not_le.1 hr).le.trans (le_max_left _ _))
                rw [indicator_of_mem (show s ∈ {s : ℝ≥0 | (s:ℝ) ≤ r} from h1),
                  indicator_of_mem (show s ∈ {s : ℝ≥0 | (s:ℝ) ≤ R'} from h2)]
                exact hs
              · rw [indicator_of_notMem (show s ∉ {s : ℝ≥0 | (s:ℝ) ≤ r} from h1), norm_zero]
                exact indicator_nonneg (fun _ _ => hC0) _
        _ = C * m.variation.real {s : ℝ≥0 | (s:ℝ) ≤ R'} := by
            rw [integral_indicator_const _ (hmeasS R'), smul_eq_mul, mul_comm]
  -- the kernel
  let K : ℝ → ℝ≥0 → ℝ → ℂ := fun a s u =>
    ({p : ℝ≥0 × ℝ | a * (p.1:ℝ) ≤ p.2}).indicator (fun p => Real.exp (-p.2) • φ p.1) (s, u)
  have hKslice : ∀ a s, (fun u => K a s u) =
      (Ici (a * (s:ℝ))).indicator (fun u : ℝ => Real.exp (-u) • φ s) := by
    intro a s; funext u
    simp only [K, indicator_apply, mem_setOf_eq, mem_Ici]
  have hKslice2 : ∀ a, 0 < a → ∀ u, (fun s => K a s u) =
      fun s => Real.exp (-u) • ({s : ℝ≥0 | (s:ℝ) ≤ u / a}).indicator φ s := by
    intro a ha u; funext s
    simp only [K, indicator_apply, mem_setOf_eq, le_div_iff₀ ha, mul_comm a]
    split_ifs <;> simp
  have hKint : ∀ a, 0 < a → Integrable (Function.uncurry (K a)) (m.variation.prod volume) := by
    intro a ha
    have hmeas : AEStronglyMeasurable (Function.uncurry (K a)) (m.variation.prod volume) := by
      have : Function.uncurry (K a) = ({p : ℝ≥0 × ℝ | a * (p.1:ℝ) ≤ p.2}).indicator
          (fun p => Real.exp (-p.2) • φ p.1) := by
        funext p; rfl
      rw [this]
      refine AEStronglyMeasurable.indicator ?_ ?_
      · have h1 : AEStronglyMeasurable (fun p : ℝ≥0 × ℝ => Real.exp (-p.2))
            (m.variation.prod volume) := Continuous.aestronglyMeasurable (by fun_prop)
        exact h1.smul hφm.comp_fst
      · exact measurableSet_le (measurable_const.mul (NNReal.continuous_coe.measurable.comp measurable_fst))
          measurable_snd
    refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall fun s => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      rw [hKslice a s]
      exact (integrable_indicator_iff measurableSet_Ici).2 ((X7_exp_Ici_int _).smul_const (φ s))
    · have heq : (fun s : ℝ≥0 => ∫ u, ‖Function.uncurry (K a) (s, u)‖) =
          fun s : ℝ≥0 => Real.exp (-(a * s)) * ‖φ s‖ := by
        funext s
        simp only [Function.uncurry_apply_pair]
        have : (fun u => ‖K a s u‖) = (Ici (a * (s:ℝ))).indicator
            (fun u : ℝ => Real.exp (-u) • ‖φ s‖) := by
          funext u
          have hh := congrFun (hKslice a s) u
          rw [hh, norm_indicator_eq_indicator_norm]
          congr 1; funext u; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            smul_eq_mul]
        rw [this, X7_exp_Ici_integral, smul_eq_mul]
      rw [heq]
      refine Integrable.mono' ((hexp a ha).const_mul C) ?_ ?_
      · exact (hexp a ha).aestronglyMeasurable.mul hφm.norm
      · filter_upwards [hφb] with s hs
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_norm, mul_comm C]
        exact mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  -- the Abel integral as a double integral
  have hAbel : ∀ a : ℝ, 0 < a →
      l (abelIntegral T m a x) = ∫ u, Real.exp (-u) • Φ (u / a) := by
    intro a ha
    have e1 : l (abelIntegral T m a x) = ∫ s, Real.exp (-(a * s)) • φ s ∂m.variation := by
      simp only [abelIntegral]
      rw [← l.integral_comp_comm (hAbelInt a ha)]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [hφdef, map_smul, smul_eq_mul, Complex.real_smul]
      rw [Complex.ofReal_exp]; push_cast; ring
    have e2 : (fun s : ℝ≥0 => Real.exp (-(a * s)) • φ s) = fun s : ℝ≥0 => ∫ u, K a s u := by
      funext s; rw [hKslice a s, X7_exp_Ici_integral]
    rw [e1, e2, integral_integral_swap (hKint a ha)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [hKslice2 a ha u, integral_smul]
  have hlimfun : ∫ u, (Ioi (0:ℝ)).indicator (fun u => Real.exp (-u) • l y) u = l y := by
    rw [integral_indicator measurableSet_Ioi, integral_smul_const, integral_exp_neg_Ioi_zero,
      one_smul]
  rw [← hlimfun]
  have hDCT : Tendsto (fun a : ℝ => ∫ u, Real.exp (-u) • Φ (u / a)) (𝓝[>] 0)
      (𝓝 (∫ u, (Ioi (0:ℝ)).indicator (fun u => Real.exp (-u) • l y) u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      ((Ici (0:ℝ)).indicator (fun u => B * Real.exp (-u))) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have hI := (hKint a ha).integral_prod_right
      refine hI.aestronglyMeasurable.congr (Eventually.of_forall fun u => ?_)
      simp only [Function.uncurry_apply_pair]
      rw [hKslice2 a ha u, integral_smul]
    · filter_upwards [self_mem_nhdsWithin] with a ha
      refine Eventually.of_forall fun u => ?_
      by_cases hu : 0 ≤ u
      · rw [indicator_of_mem (show u ∈ Ici (0:ℝ) from hu), norm_smul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), mul_comm B]
        exact mul_le_mul_of_nonneg_left (hB _) (Real.exp_pos _).le
      · have hneg : u / a < 0 := div_neg_of_neg_of_pos (not_le.1 hu) ha
        rw [hΦneg _ hneg, smul_zero, norm_zero]
        exact indicator_nonneg (fun u _ => by positivity) _
    · exact (integrable_indicator_iff measurableSet_Ici).2 ((X7_exp_Ici_int 0).const_mul B)
    · have hae : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
        rw [ae_iff]; simp
      filter_upwards [hae] with u hu
      rcases lt_or_gt_of_ne hu with hu | hu
      · rw [indicator_of_notMem (show u ∉ Ioi (0:ℝ) from not_lt.2 hu.le)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with a ha
        rw [hΦneg _ (div_neg_of_neg_of_pos hu ha), smul_zero]
      · rw [indicator_of_mem (show u ∈ Ioi (0:ℝ) from hu)]
        refine Tendsto.const_smul (hΦlim.comp ?_) _
        have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hu
        exact this.congr (fun a => (div_eq_mul_inv u a).symm)
  refine hDCT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (hAbel a ha).symm

end QAlgorithms.Papers.Independent.Gap48.P07

end

universe u

noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P07 QAlgorithms.Papers.Independent.Next46.P06 in
theorem solution {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] :
    (∀ (T : ℝ → X →L[ℂ] X), BoundedC0 T → ∀ (m : LaplaceRadon) (x y : X),
      WeakImproper T m x y → WeakAbel T m x y) ∧
    (∀ a : ℝ, a ≠ 0 → ∀ x : X, x ≠ 0 →
      (∀ alpha : ℝ, 0 < alpha → IntegrableOn
        (fun s : ℝ => Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x)
        (Ici 0)) ∧
      (∀ l : X →L[ℂ] ℂ, Tendsto
        (fun alpha : ℝ => l (∫ s in Ici (0 : ℝ),
          Complex.exp ((-(alpha : ℂ) + Complex.I * (a : ℂ)) * (s : ℂ)) • x))
        (𝓝[>] 0) (𝓝 (l ((-Complex.I * (a : ℂ))⁻¹ • x)))) ∧
      (∀ r : ℝ, 0 ≤ r → (∫ s in Icc (0 : ℝ) r,
        Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x) =
        ((Complex.exp (Complex.I * (a : ℂ) * (r : ℂ)) - 1) / (Complex.I * (a : ℂ))) • x) ∧
      ¬ ∃ y : X, ∀ l : X →L[ℂ] ℂ, Tendsto
        (fun r : ℝ => l (∫ s in Icc (0 : ℝ) r,
          Complex.exp (Complex.I * (a : ℂ) * (s : ℂ)) • x)) atTop (𝓝 (l y))) :=
  ⟨fun T hT m x y h => X7_part1 T hT m x y h, fun a ha x hx => X7_part2 a ha x hx⟩

end
