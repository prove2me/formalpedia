-- Prove2me | solution 1 for QueueingFundamentals.Transient.busy_period_laplace
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:05:49.593974+00:00
-- url     : https://prove2.me/submissions/8e5e2538-9b36-41ea-8842-e457cb35b867

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_forwardEquations
import Definitions.Def_QueueingFundamentals_Transient_laplace



namespace QueueingFundamentals.Transient

open Filter Topology MeasureTheory

lemma qla_le_one {q : ℕ → ℝ → ℝ} (hprob : IsProbabilityFamily q) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    q n t ≤ 1 := by
  rw [← (hprob t ht).2.tsum_eq]
  exact (hprob t ht).2.summable.le_tsum n (fun k _ => (hprob t ht).1 k)

lemma qla_integrable {q : ℕ → ℝ → ℝ} (hprob : IsProbabilityFamily q)
    (hc : ContinuousOn (q 0) (Set.Ici 0)) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ)) (Set.Ioi 0) := by
  have hb := exp_neg_integrableOn_Ioi 0 hs
  refine Integrable.mono' hb ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    have : ContinuousOn (fun t : ℝ => (q 0 t : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn (hc.mono Set.Ioi_subset_Ici_self)
    exact (Continuous.continuousOn (by fun_prop)).mul this
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun t ht => ?_)
    have ht0 : (0:ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((hprob t ht0).1 0)]
    have : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [this]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (qla_le_one hprob ht0 0)

/-- General Laplace-transform lemma via a dual eigen-sequence. -/
lemma qla_main (q : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hder : ∀ n t, 0 ≤ t → HasDerivWithinAt (q n) (F n t) (Set.Ici 0) t)
    (hFc : ∀ n, ContinuousOn (F n) (Set.Ici 0))
    (hprob : IsProbabilityFamily q) (v : ℕ → ℂ) (hv : ∀ n, ‖v n‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (K : ℂ) (C ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hid : ∀ N : ℕ, ∀ t, 0 ≤ t →
      ‖∑ n ∈ Finset.range (N + 1), (F n t : ℂ) * v n
        - (s * ∑ n ∈ Finset.range (N + 1), (q n t : ℂ) * v n + K * q 0 t)‖ ≤ C * ρ ^ N) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ)) (Set.Ioi 0) ∧
      K * laplace (q 0) s = -∑' n, (q n 0 : ℂ) * v n := by
  have hqc : ∀ n, ContinuousOn (q n) (Set.Ici 0) := fun n t ht => (hder n t ht).continuousWithinAt
  have hint := qla_integrable hprob (hqc 0) s hs
  refine ⟨hint, ?_⟩
  -- summability of the pairing
  have hsum : ∀ t, 0 ≤ t → HasSum (fun n => (q n t : ℂ) * v n) (∑' n, (q n t : ℂ) * v n) := by
    intro t ht
    refine Summable.hasSum ?_
    refine Summable.of_norm_bounded (hprob t ht).2.summable (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hprob t ht).1 n)]
    exact mul_le_of_le_one_right ((hprob t ht).1 n) (hv n)
  set S : ℝ → ℂ := fun t => ∑' n, (q n t : ℂ) * v n with hSdef
  set I : ℝ → ℂ := fun T => ∫ t in (0:ℝ)..T, Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ) with hIdef
  -- finite-time identity
  have hfin : ∀ T : ℝ, 0 ≤ T → Complex.exp (-s * (T : ℂ)) * S T - S 0 = K * I T := by
    intro T hT
    have hsub : Set.Icc 0 T ⊆ Set.Ici (0:ℝ) := fun t ht => ht.1
    have hqcC : ∀ n, ContinuousOn (fun t : ℝ => (q n t : ℂ)) (Set.Icc 0 T) := fun n =>
      Complex.continuous_ofReal.comp_continuousOn ((hqc n).mono hsub)
    have hFcC : ∀ n, ContinuousOn (fun t : ℝ => (F n t : ℂ)) (Set.Icc 0 T) := fun n =>
      Complex.continuous_ofReal.comp_continuousOn ((hFc n).mono hsub)
    have hEc : Continuous (fun t : ℝ => Complex.exp (-s * (t : ℂ))) := by fun_prop
    -- error bound for each N
    have hN : ∀ N : ℕ, ‖(Complex.exp (-s * (T : ℂ)) * ∑ n ∈ Finset.range (N + 1), (q n T : ℂ) * v n
        - ∑ n ∈ Finset.range (N + 1), (q n 0 : ℂ) * v n) - K * I T‖ ≤ C * ρ ^ N * T := by
      intro N
      set G : ℝ → ℂ := fun t => ∑ n ∈ Finset.range (N + 1), (q n t : ℂ) * v n with hG
      set D : ℝ → ℂ := fun t => ∑ n ∈ Finset.range (N + 1), (F n t : ℂ) * v n with hD
      have hGc : ContinuousOn G (Set.Icc 0 T) := by
        apply continuousOn_finsetSum; intro n _; exact (hqcC n).mul continuousOn_const
      have hDc : ContinuousOn D (Set.Icc 0 T) := by
        apply continuousOn_finsetSum; intro n _; exact (hFcC n).mul continuousOn_const
      have hftc : ∫ t in (0:ℝ)..T, Complex.exp (-s * (t : ℂ)) * (D t - s * G t)
          = Complex.exp (-s * (T : ℂ)) * G T - Complex.exp (-s * ((0:ℝ) : ℂ)) * G 0 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
        · exact hEc.continuousOn.mul hGc
        · intro t ht
          have hs0 : Set.Ici (0:ℝ) ∈ 𝓝 t := Ici_mem_nhds ht.1
          have hGd : HasDerivAt G (D t) t := by
            rw [hG, hD]
            apply HasDerivAt.fun_sum
            intro n _
            have h1 := ((hder n t ht.1.le).hasDerivAt hs0).ofReal_comp
            exact h1.mul_const (v n)
          have hEd : HasDerivAt (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
              (Complex.exp (-s * (t : ℂ)) * (-s)) t := by
            have := ((hasDerivAt_id t).ofReal_comp.const_mul (-s)).cexp
            simpa using this
          have := hEd.mul hGd
          refine this.congr_deriv ?_
          ring
        · apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hT]
          exact hEc.continuousOn.mul (hDc.sub (continuousOn_const.mul hGc))
      have hIint : IntervalIntegrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ))
          volume 0 T := by
        apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]
        exact hEc.continuousOn.mul (hqcC 0)
      have hDint : IntervalIntegrable (fun t => Complex.exp (-s * (t : ℂ)) * (D t - s * G t))
          volume 0 T := by
        apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le hT]
        exact hEc.continuousOn.mul (hDc.sub (continuousOn_const.mul hGc))
      have hdiff : (Complex.exp (-s * (T : ℂ)) * G T - G 0) - K * I T
          = ∫ t in (0:ℝ)..T, (Complex.exp (-s * (t : ℂ)) * (D t - s * G t)
              - K * (Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ))) := by
        rw [intervalIntegral.integral_sub hDint (hIint.const_mul K), hftc,
          intervalIntegral.integral_const_mul]
        simp [hIdef]
      rw [show (Complex.exp (-s * (T : ℂ)) * ∑ n ∈ Finset.range (N + 1), (q n T : ℂ) * v n
        - ∑ n ∈ Finset.range (N + 1), (q n 0 : ℂ) * v n) = Complex.exp (-s * (T : ℂ)) * G T - G 0
        from rfl, hdiff]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := C * ρ ^ N)
        (f := fun t => Complex.exp (-s * (t : ℂ)) * (D t - s * G t)
              - K * (Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ))) ?_
      · rwa [sub_zero, abs_of_nonneg hT] at this
      · intro t ht
        rw [Set.uIoc_of_le hT] at ht
        have ht0 : (0:ℝ) ≤ t := le_of_lt ht.1
        have he : ‖Complex.exp (-s * (t : ℂ))‖ ≤ 1 := by
          rw [Complex.norm_exp]
          apply Real.exp_le_one_iff.2
          simp; nlinarith
        have h1 := hid N t ht0
        calc ‖Complex.exp (-s * (t : ℂ)) * (D t - s * G t)
              - K * (Complex.exp (-s * (t : ℂ)) * (q 0 t : ℂ))‖
            = ‖Complex.exp (-s * (t : ℂ))‖ * ‖D t - (s * G t + K * q 0 t)‖ := by
              rw [← norm_mul]; congr 1; ring
          _ ≤ 1 * (C * ρ ^ N) := by
              apply mul_le_mul he h1 (norm_nonneg _) zero_le_one
          _ = C * ρ ^ N := one_mul _
    -- pass to the limit N → ∞
    have hlimL : Tendsto (fun N : ℕ => (Complex.exp (-s * (T : ℂ)) *
        ∑ n ∈ Finset.range (N + 1), (q n T : ℂ) * v n
        - ∑ n ∈ Finset.range (N + 1), (q n 0 : ℂ) * v n) - K * I T) atTop
        (𝓝 ((Complex.exp (-s * (T : ℂ)) * S T - S 0) - K * I T)) := by
      have h1 := ((hsum T hT).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
      have h2 := ((hsum 0 le_rfl).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
      exact ((h1.const_mul _).sub h2).sub tendsto_const_nhds
    have hlim0 : Tendsto (fun N : ℕ => (Complex.exp (-s * (T : ℂ)) *
        ∑ n ∈ Finset.range (N + 1), (q n T : ℂ) * v n
        - ∑ n ∈ Finset.range (N + 1), (q n 0 : ℂ) * v n) - K * I T) atTop (𝓝 0) := by
      have hg : Tendsto (fun N : ℕ => C * ρ ^ N * T) atTop (𝓝 0) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C).mul_const T
        simpa using this
      exact squeeze_zero_norm hN hg
    have := tendsto_nhds_unique hlimL hlim0
    exact sub_eq_zero.1 this
  -- pass to the limit T → ∞
  have hS : ∀ t, 0 ≤ t → ‖S t‖ ≤ 1 := by
    intro t ht
    have h := (hsum t ht).norm_le_of_bounded (g := fun n => q n t) (hprob t ht).2 (fun n => ?_)
    · exact h
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((hprob t ht).1 n)]
      exact mul_le_of_le_one_right ((hprob t ht).1 n) (hv n)
  have hI := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hE0 : Tendsto (fun T : ℝ => Complex.exp (-s * (T : ℂ)) * S T) atTop (𝓝 0) := by
    have hg : Tendsto (fun T : ℝ => Real.exp (-s.re * T)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atTop.comp ((tendsto_id.const_mul_atTop hs))
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hs)
      refine h2.congr (fun T => ?_)
      simp [Function.comp]
    refine squeeze_zero_norm' ?_ hg
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    rw [norm_mul, Complex.norm_exp]
    have : (-s * (T : ℂ)).re = -s.re * T := by simp
    rw [this]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hS T hT)
  have hL : Tendsto (fun T : ℝ => Complex.exp (-s * (T : ℂ)) * S T - S 0) atTop (𝓝 (0 - S 0)) :=
    hE0.sub tendsto_const_nhds
  have hR : Tendsto (fun T : ℝ => K * I T) atTop (𝓝 (K * laplace (q 0) s)) := by
    unfold laplace
    exact hI.const_mul K
  have hEq : Tendsto (fun T : ℝ => Complex.exp (-s * (T : ℂ)) * S T - S 0) atTop
      (𝓝 (K * laplace (q 0) s)) := by
    refine hR.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    exact (hfin T hT).symm
  have := tendsto_nhds_unique hEq hL
  rw [this, zero_sub]

lemma qla_root (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    let z := ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))
    z ≠ 0 ∧ ‖z‖ < 1 ∧ (lam : ℂ) * z ^ 2 - ((lam : ℂ) + (mu : ℂ) + s) * z + (mu : ℂ) = 0 ∧
      ((lam : ℂ) + (mu : ℂ) + s + r) * z = 2 * (mu : ℂ) := by
  intro z
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hm : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
  set b : ℂ := (lam : ℂ) + (mu : ℂ) + s with hb
  have h1 : b - r = 2 * lam * z := by simp only [z]; field_simp; rw [hb]
  have h2 : (b + r) * z = 2 * mu := by
    have : (b + r) * (b - r) = 4 * lam * mu := by linear_combination -hr
    rw [h1] at this
    have h3 : (2 * (lam:ℂ)) * ((b + r) * z - 2 * mu) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h3 with h | h
    · exfalso; exact two_ne_zero (mul_eq_zero.1 h |>.resolve_right hl)
    · linear_combination h
  have hz0 : z ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact two_ne_zero (mul_eq_zero.1 h2.symm |>.resolve_right hm)
  have hroot : (lam : ℂ) * z ^ 2 - b * z + (mu : ℂ) = 0 := by
    have : b = lam * z + mu * z⁻¹ := by
      have e1 : b + r = 2 * mu * z⁻¹ := by
        rw [← h2]; field_simp
      linear_combination (h1 + e1) / 2
    rw [this]; field_simp; ring
  refine ⟨hz0, ?_, hroot, h2⟩
  -- norm bound
  have e1 : b + r = 2 * mu * z⁻¹ := by rw [← h2]; field_simp
  have hbz : b = lam * z + mu * z⁻¹ := by linear_combination (h1 + e1) / 2
  have hrz : r = mu * z⁻¹ - lam * z := by linear_combination (e1 - h1) / 2
  have hbre : b.re = lam * z.re + mu * (z.re / Complex.normSq z) := by
    rw [hbz]; simp [Complex.inv_re]
  have hrre : r.re = mu * (z.re / Complex.normSq z) - lam * z.re := by
    rw [hrz]; simp [Complex.inv_re]
  have hbre' : b.re = lam + mu + s.re := by rw [hb]; simp
  have hN : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have hx2 : z.re ^ 2 ≤ Complex.normSq z := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
  rw [Complex.norm_def]
  by_contra hcon
  push_neg at hcon
  set N := Complex.normSq z with hNdef
  set x := z.re with hxdef
  set ρ := Real.sqrt N with hρ
  have hρ1 : 1 ≤ ρ := hcon
  have hρ2 : ρ ^ 2 = N := Real.sq_sqrt hN.le
  set w := x / N with hw
  have hxw : x = w * N := by rw [hw]; field_simp
  have hA : 0 < w * (mu - lam * N) := by
    have : 0 < mu * w - lam * x := by rw [← hrre]; exact hr_re
    rw [hxw] at this; nlinarith
  have hB : lam + mu < w * (lam * N + mu) := by
    have : lam + mu < lam * x + mu * w := by rw [← hbre, hbre']; linarith
    rw [hxw] at this; nlinarith
  have hwpos : 0 < w := by
    by_contra hw0; push_neg at hw0
    have : w * (lam * N + mu) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw0 (by positivity)
    linarith
  have hmuN : lam * N < mu := by
    have := (pos_iff_pos_of_mul_pos hA).1 hwpos; linarith
  have hwρ : w * ρ ≤ 1 := by
    have h3 : (w * ρ) ^ 2 ≤ 1 := by
      rw [mul_pow, hρ2]
      have : x ^ 2 = w ^ 2 * N ^ 2 := by rw [hxw]; ring
      rw [this] at hx2
      have : w ^ 2 * N ≤ 1 := by
        by_contra h; push_neg at h; nlinarith
      linarith
    nlinarith [mul_pos hwpos (lt_of_lt_of_le one_pos hρ1)]
  have hB2 : (lam + mu) * ρ < lam * ρ ^ 2 + mu := by
    rw [hρ2]
    have hpos : 0 < lam * N + mu := by positivity
    have := mul_le_mul_of_nonneg_right hwρ hpos.le
    nlinarith
  have hmu2 : lam * ρ ≤ mu := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hρ1) (sub_nonneg.2 hmu2)]

lemma qla_mm1_cont {lam mu : ℝ} {q : ℕ → ℝ → ℝ} (hsol : IsForwardSolution (mm1RHS lam mu) q)
    (n : ℕ) : ContinuousOn (fun t => mm1RHS lam mu (fun m => q m t) n) (Set.Ici 0) := by
  have hc : ∀ n, ContinuousOn (q n) (Set.Ici 0) := fun n t ht => (hsol n t ht).continuousWithinAt
  cases n with
  | zero =>
    simp only [mm1RHS]
    have h1 := hc 0
    have h2 := hc 1
    fun_prop
  | succ n =>
    simp only [mm1RHS]
    have h1 := hc (n + 1)
    have h2 := hc n
    have h3 := hc (n + 2)
    fun_prop

theorem mm1_laplace_p0_core (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i : ℕ)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (mm1RHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = i then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s
        = (((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ))) ^ (i + 1)
          / ((mu : ℂ) * (1 - ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ)))) := by
  obtain ⟨hz0, hz1, hroot, -⟩ := qla_root lam mu hlam hmu s hs r hr hr_re
  set z := ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ)) with hzdef
  clear_value z
  have hzinv : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hident : ∀ N : ℕ, ∀ t,
      ∑ n ∈ Finset.range (N + 1), (mm1RHS lam mu (fun m => p m t) n : ℂ) * z ^ n
        - (s * ∑ n ∈ Finset.range (N + 1), (p n t : ℂ) * z ^ n + (-(mu : ℂ) * (z⁻¹ - 1)) * p 0 t)
      = -(lam : ℂ) * p N t * z ^ (N + 1) + (mu : ℂ) * p (N + 1) t * z ^ N := by
    intro N t
    induction N with
    | zero =>
      simp only [Finset.sum_range_one, mm1RHS, pow_zero, mul_one, zero_add, pow_one]
      push_cast
      linear_combination ((p 0 t : ℂ) * z⁻¹) * hroot
        - ((lam : ℂ) * (p 0 t : ℂ) * z - ((lam : ℂ) + mu + s) * (p 0 t : ℂ)) * hzinv
    | succ N ih =>
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1)]
      have hF : (mm1RHS lam mu (fun m => p m t) (N + 1) : ℂ)
          = -((lam : ℂ) + mu) * p (N + 1) t + lam * p N t + mu * p (N + 2) t := by
        simp [mm1RHS]
      rw [hF]
      linear_combination ih + ((p (N + 1) t : ℂ) * z ^ N) * hroot
  have hnz : ‖z‖ < 1 := hz1
  have h := qla_main p (fun n t => mm1RHS lam mu (fun m => p m t) n) hsol
    (qla_mm1_cont hsol) hprob (fun n => z ^ n)
    (fun n => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hnz.le)
    s hs (-(mu : ℂ) * (z⁻¹ - 1)) (lam + mu) ‖z‖ (norm_nonneg _) hnz ?_
  · obtain ⟨hint, hK⟩ := h
    refine ⟨hint, ?_⟩
    have hS : ∑' n, (p n 0 : ℂ) * z ^ n = z ^ i := by
      rw [tsum_eq_single i]
      · simp [hinit]
      · intro b hb; simp [hinit, hb]
    rw [hS] at hK
    have h1z : (1 : ℂ) - z ≠ 0 := by
      intro h
      have : z = 1 := by linear_combination -h
      rw [this, norm_one] at hnz; exact lt_irrefl _ hnz
    have hmu' : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
    have hK' : (-(mu : ℂ) * (z⁻¹ - 1)) ≠ 0 := by
      have : -(mu : ℂ) * (z⁻¹ - 1) = -(mu : ℂ) * (1 - z) / z := by field_simp
      rw [this]
      exact div_ne_zero (mul_ne_zero (neg_ne_zero.2 hmu') h1z) hz0
    have : laplace (p 0) s = -z ^ i / (-(mu : ℂ) * (z⁻¹ - 1)) := by
      rw [eq_div_iff hK', ← hK]; ring
    rw [this]
    field_simp
    ring
  · intro N t ht
    rw [hident N t]
    have hp0 := (hprob t ht).1 N
    have hp1 := (hprob t ht).1 (N + 1)
    have hq0 := qla_le_one hprob ht N
    have hq1 := qla_le_one hprob ht (N + 1)
    calc ‖-(lam : ℂ) * p N t * z ^ (N + 1) + (mu : ℂ) * p (N + 1) t * z ^ N‖
        ≤ ‖-(lam : ℂ) * p N t * z ^ (N + 1)‖ + ‖(mu : ℂ) * p (N + 1) t * z ^ N‖ := norm_add_le _ _
      _ = lam * p N t * ‖z‖ ^ (N + 1) + mu * p (N + 1) t * ‖z‖ ^ N := by
          simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow,
            abs_of_pos hlam, abs_of_pos hmu, abs_of_nonneg hp0, abs_of_nonneg hp1]
      _ ≤ lam * 1 * ‖z‖ ^ N + mu * 1 * ‖z‖ ^ N := by
          have hzN : ‖z‖ ^ (N + 1) ≤ ‖z‖ ^ N :=
            pow_le_pow_of_le_one (norm_nonneg _) hnz.le (by omega)
          have hzp : 0 ≤ ‖z‖ ^ N := by positivity
          gcongr
      _ = (lam + mu) * ‖z‖ ^ N := by ring

lemma qla_busy_cont {lam mu : ℝ} {q : ℕ → ℝ → ℝ} (hsol : IsForwardSolution (busyRHS lam mu) q)
    (n : ℕ) : ContinuousOn (fun t => busyRHS lam mu (fun m => q m t) n) (Set.Ici 0) := by
  have hc : ∀ n, ContinuousOn (q n) (Set.Ici 0) := fun n t ht => (hsol n t ht).continuousWithinAt
  rcases n with _ | _ | n
  · simp only [busyRHS]
    have h1 := hc 1
    fun_prop
  · simp only [busyRHS]
    have h1 := hc 1
    have h2 := hc 2
    fun_prop
  · simp only [busyRHS]
    have h1 := hc (n + 2)
    have h2 := hc (n + 1)
    have h3 := hc (n + 3)
    fun_prop

theorem busy_period_laplace_core (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (busyRHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = 1 then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s = 2 * (mu : ℂ) / (s * ((lam : ℂ) + (mu : ℂ) + s + r)) := by
  obtain ⟨hz0, hz1, hroot, hbr⟩ := qla_root lam mu hlam hmu s hs r hr hr_re
  set z := ((lam : ℂ) + (mu : ℂ) + s - r) / (2 * (lam : ℂ)) with hzdef
  clear_value z
  set v : ℕ → ℂ := fun n => if n = 0 then 1 else z ^ n with hv
  have hv0 : v 0 = 1 := by simp [hv]
  have hvs : ∀ n, v (n + 1) = z ^ (n + 1) := by intro n; simp [hv]
  have hident : ∀ N : ℕ, ∀ t,
      ∑ n ∈ Finset.range (N + 1), (busyRHS lam mu (fun m => p m t) n : ℂ) * v n
        - (s * ∑ n ∈ Finset.range (N + 1), (p n t : ℂ) * v n + (-s) * p 0 t)
      = (if N = 0 then 0 else -(lam : ℂ) * p N t * z ^ (N + 1)) + (mu : ℂ) * p (N + 1) t * z ^ N := by
    intro N t
    induction N with
    | zero =>
      simp only [Finset.sum_range_one, busyRHS, hv0, if_true, pow_zero, mul_one, zero_add]
      push_cast; ring
    | succ N ih =>
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1), hvs N]
      rcases N with _ | N
      · have hF : (busyRHS lam mu (fun m => p m t) (0 + 1) : ℂ)
            = -((lam : ℂ) + mu) * p 1 t + mu * p 2 t := by simp [busyRHS]
        rw [hF]
        simp only [if_true] at ih
        simp only [zero_add, one_ne_zero, if_false] at ih ⊢
        linear_combination ih + ((p 1 t : ℂ)) * hroot
      · have hF : (busyRHS lam mu (fun m => p m t) (N + 1 + 1) : ℂ)
            = -((lam : ℂ) + mu) * p (N + 2) t + lam * p (N + 1) t + mu * p (N + 3) t := by
          simp [busyRHS]
        rw [hF]
        simp only [Nat.add_one_ne_zero, if_false] at ih ⊢
        linear_combination ih + ((p (N + 2) t : ℂ) * z ^ (N + 1)) * hroot
  have hnz : ‖z‖ < 1 := hz1
  have hvb : ∀ n, ‖v n‖ ≤ 1 := by
    intro n; rcases n with _ | n
    · simp [hv0]
    · rw [hvs, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hnz.le
  have h := qla_main p (fun n t => busyRHS lam mu (fun m => p m t) n) hsol
    (qla_busy_cont hsol) hprob v hvb s hs (-s) (lam + mu) ‖z‖ (norm_nonneg _) hnz ?_
  · obtain ⟨hint, hK⟩ := h
    refine ⟨hint, ?_⟩
    have hS : ∑' n, (p n 0 : ℂ) * v n = z := by
      rw [tsum_eq_single 1]
      · simp [hinit, hvs 0]
      · intro b hb; simp [hinit, hb]
    rw [hS] at hK
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have hbr0 : (lam : ℂ) + mu + s + r ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hl : laplace (p 0) s = z / s := by
      rw [eq_div_iff hs0]; linear_combination -hK
    rw [hl, eq_div_iff (mul_ne_zero hs0 hbr0)]
    field_simp
    linear_combination hbr
  · intro N t ht
    rw [hident N t]
    have hp0 := (hprob t ht).1 N
    have hp1 := (hprob t ht).1 (N + 1)
    have hq0 := qla_le_one hprob ht N
    have hq1 := qla_le_one hprob ht (N + 1)
    have hzN : ‖z‖ ^ (N + 1) ≤ ‖z‖ ^ N := pow_le_pow_of_le_one (norm_nonneg _) hnz.le (by omega)
    have hzp : 0 ≤ ‖z‖ ^ N := by positivity
    have hA : ‖(if N = 0 then (0:ℂ) else -(lam : ℂ) * p N t * z ^ (N + 1))‖ ≤ lam * ‖z‖ ^ N := by
      split_ifs
      · simp; positivity
      · simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_pow,
          abs_of_pos hlam, abs_of_nonneg hp0]
        calc lam * p N t * ‖z‖ ^ (N + 1) ≤ lam * 1 * ‖z‖ ^ N := by gcongr
          _ = lam * ‖z‖ ^ N := by ring
    have hB : ‖(mu : ℂ) * p (N + 1) t * z ^ N‖ ≤ mu * ‖z‖ ^ N := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
        abs_of_pos hmu, abs_of_nonneg hp1]
      calc mu * p (N + 1) t * ‖z‖ ^ N ≤ mu * 1 * ‖z‖ ^ N := by gcongr
        _ = mu * ‖z‖ ^ N := by ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ lam * ‖z‖ ^ N + mu * ‖z‖ ^ N := add_le_add hA hB
      _ = (lam + mu) * ‖z‖ ^ N := by ring

end QueueingFundamentals.Transient

open QueueingFundamentals.Transient
open MeasureTheory

theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (p : ℕ → ℝ → ℝ) (hsol : IsForwardSolution (busyRHS lam mu) p)
    (hprob : IsProbabilityFamily p) (hinit : ∀ n : ℕ, p n 0 = if n = 1 then 1 else 0)
    (s : ℂ) (hs : 0 < s.re) (r : ℂ)
    (hr : r ^ 2 = ((lam : ℂ) + (mu : ℂ) + s) ^ 2 - 4 * (lam : ℂ) * (mu : ℂ))
    (hr_re : 0 < r.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (p 0 t : ℂ)) (Set.Ioi 0) ∧
      laplace (p 0) s = 2 * (mu : ℂ) / (s * ((lam : ℂ) + (mu : ℂ) + s + r)) := by
  exact busy_period_laplace_core lam mu hlam hmu p hsol hprob hinit s hs r hr hr_re
