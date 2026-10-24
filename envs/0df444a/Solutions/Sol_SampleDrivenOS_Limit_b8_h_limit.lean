-- Prove2me | solution 1 for SampleDrivenOS.Limit.b8_h_limit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:02:55.865728+00:00
-- url     : https://prove2.me/submissions/683c395a-688e-4dee-9fc0-1a27583b8008

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace B8Aux

/-- `φ_k(x) = 1 / (x(1 - k ln x) + 1/η - 1)` -/
noncomputable def phi (η k x : ℝ) : ℝ := 1 / (x * (1 - k * Real.log x) + 1 / η - 1)

noncomputable def J (η k : ℝ) : ℝ := ∫ x in (0:ℝ)..1, phi η k x

lemma c_pos (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) : 0 < 1 / η - 1 := by
  rw [sub_pos, lt_one_div (by norm_num) hη0]; simpa using hη1

lemma psi_nonneg (k x : ℝ) (hk : 0 ≤ k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x * (1 - k * Real.log x) := by
  have := Real.log_nonpos hx0 hx1
  apply mul_nonneg hx0
  nlinarith

lemma psi_cont (k : ℝ) : Continuous (fun x : ℝ => x * (1 - k * Real.log x)) := by
  have : (fun x : ℝ => x * (1 - k * Real.log x)) = fun x => x - k * (x * Real.log x) := by
    funext x; ring
  rw [this]
  exact continuous_id.sub (continuous_const.mul Real.continuous_mul_log)

lemma phi_contOn (η k : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk : 0 ≤ k) :
    ContinuousOn (phi η k) (Set.Icc 0 1) := by
  have hc := c_pos η hη0 hη1
  have : phi η k = fun x => 1 / (x * (1 - k * Real.log x) + (1 / η - 1)) := by
    funext x; unfold phi; ring_nf
  rw [this]
  apply ContinuousOn.div continuousOn_const ((psi_cont k).add continuous_const).continuousOn
  intro x hx
  have := psi_nonneg k x hk hx.1 hx.2
  apply ne_of_gt
  simp only [Pi.add_apply]
  linarith

lemma phi_nonneg (η k x : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk : 0 ≤ k) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : 0 ≤ phi η k x := by
  have hc := c_pos η hη0 hη1
  have := psi_nonneg k x hk hx0 hx1
  unfold phi
  apply div_nonneg zero_le_one
  linarith

lemma phi_le (η k x : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk : 0 ≤ k) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) : phi η k x ≤ 1 / (1 / η - 1) := by
  have hc := c_pos η hη0 hη1
  have := psi_nonneg k x hk hx0 hx1
  unfold phi
  apply one_div_le_one_div_of_le hc
  linarith

lemma psi_mono (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    MonotoneOn (fun x : ℝ => x * (1 - k * Real.log x)) (Set.Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (psi_cont k).continuousOn
  · rw [interior_Icc]
    intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.mul differentiableAt_id
    apply DifferentiableAt.sub (differentiableAt_const _)
    exact (Real.differentiableAt_log hx.1.ne').const_mul _
  · rw [interior_Icc]
    intro x hx
    have hd : HasDerivAt (fun x : ℝ => x * (1 - k * Real.log x))
        (1 * (1 - k * Real.log x) + x * (0 - k * x⁻¹)) x := by
      apply HasDerivAt.mul (hasDerivAt_id x)
      apply HasDerivAt.sub (hasDerivAt_const _ _)
      exact (Real.hasDerivAt_log hx.1.ne').const_mul k
    rw [hd.deriv]
    have hl := Real.log_nonpos hx.1.le hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have : x * (0 - k * x⁻¹) = -k := by field_simp; ring
    rw [this]
    nlinarith

lemma phi_anti (η k : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    AntitoneOn (phi η k) (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hc := c_pos η hη0 hη1
  have h1 := psi_mono k hk0 hk1 hx hy hxy
  have h0 := psi_nonneg k x hk0 hx.1 hx.2
  simp only at h1
  unfold phi
  apply one_div_le_one_div_of_le (by linarith)
  linarith

/-- two-sided bound of an antitone function's integral on a subinterval -/
lemma int_bounds (η k a b : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * phi η k b ≤ ∫ x in a..b, phi η k x ∧ ∫ x in a..b, phi η k x ≤ (b - a) * phi η k a := by
  have hcont : ContinuousOn (phi η k) (Set.Icc a b) :=
    (phi_contOn η k hη0 hη1 hk0).mono (Set.Icc_subset_Icc ha hb)
  have hint : IntervalIntegrable (phi η k) volume a b := hcont.intervalIntegrable_of_Icc hab
  have hanti := phi_anti η k hη0 hη1 hk0 hk1
  constructor
  · have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := phi η k b)) hint
      (fun x hx => hanti ⟨le_trans ha hx.1, le_trans hx.2 hb⟩ ⟨le_trans ha hab, hb⟩ hx.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  · have := intervalIntegral.integral_mono_on hab hint (intervalIntegrable_const (c := phi η k a))
      (fun x hx => hanti ⟨ha, le_trans hab hb⟩ ⟨le_trans ha hx.1, le_trans hx.2 hb⟩ hx.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this

lemma int_intble (η k a b : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k)
    (ha : 0 ≤ a) (hb : b ≤ 1) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) :
    IntervalIntegrable (phi η k) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (phi_contOn η k hη0 hη1 hk0).mono
  intro x hx
  rw [Set.mem_uIcc] at hx
  rcases hx with h | h
  · exact ⟨le_trans ha h.1, le_trans h.2 hb⟩
  · exact ⟨le_trans hb0 h.1, le_trans h.2 ha1⟩

/-- telescoping: `Σ_{i<n} ∫_{r^{i+1}}^{r^i} φ = J - ∫_0^{r^n} φ` -/
lemma tele (η k r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k) (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫ x in r ^ (i + 1)..r ^ i, phi η k x
      = J η k - ∫ x in (0:ℝ)..r ^ n, phi η k x := by
  have hpow : ∀ j : ℕ, 0 ≤ r ^ j ∧ r ^ j ≤ 1 := fun j =>
    ⟨pow_nonneg hr0.le _, pow_le_one₀ hr0.le hr1.le⟩
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := phi η k)
    (a := fun j => r ^ j) (n := n)
    (fun j _ => int_intble η k _ _ hη0 hη1 hk0 (hpow j).1 (hpow (j+1)).2 (hpow j).2 (hpow (j+1)).1)
  have h1 : ∑ i ∈ Finset.range n, ∫ x in r ^ (i + 1)..r ^ i, phi η k x
      = -∑ i ∈ Finset.range n, ∫ x in r ^ i..r ^ (i + 1), phi η k x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_symm]
  rw [h1, hsum]
  simp only [pow_zero]
  unfold J
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := r ^ n)
    (int_intble η k _ _ hη0 hη1 hk0 le_rfl (hpow n).2 zero_le_one (hpow n).1)
    (int_intble η k _ _ hη0 hη1 hk0 (hpow n).1 le_rfl (hpow n).2 zero_le_one),
    intervalIntegral.integral_symm]
  ring

lemma small_int (η k r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ ∫ x in (0:ℝ)..r, phi η k x ∧ ∫ x in (0:ℝ)..r, phi η k x ≤ r * (1 / (1 / η - 1)) := by
  obtain ⟨-, h2⟩ := int_bounds η k 0 r hη0 hη1 hk0 hk1 le_rfl hr0 hr1
  constructor
  · apply intervalIntegral.integral_nonneg hr0
    intro x hx
    exact phi_nonneg η k x hη0 hη1 hk0 hx.1 (le_trans hx.2 hr1)
  · refine le_trans h2 ?_
    simp only [sub_zero]
    apply mul_le_mul_of_nonneg_left _ hr0
    unfold phi; simp

/-- the Riemann-sum terms -/
noncomputable def dterm (η r : ℝ) (i : ℕ) : ℝ :=
  r ^ i * (1 - r) / ((((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)) + 1 / η - 1)

noncomputable def kap (r : ℝ) : ℝ := (1 - r) / (-Real.log r)

lemma kap_bounds (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : 0 < kap r ∧ kap r ≤ 1 := by
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  have hl2 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr0
  unfold kap
  constructor
  · apply div_pos (by linarith) (by linarith)
  · rw [div_le_one (by linarith)]; linarith

lemma dterm_eq (η r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (i : ℕ) :
    dterm η r i = (r ^ i - r ^ (i + 1)) * phi η (kap r) (r ^ (i + 1)) := by
  have hl : Real.log r ≠ 0 := (Real.log_neg hr0 hr1).ne
  unfold dterm phi kap
  rw [Real.log_pow]
  have : (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)) =
      r ^ (i + 1) * (1 - (1 - r) / -Real.log r * (((i + 1 : ℕ) : ℝ) * Real.log r)) := by
    push_cast
    field_simp
    ring
  rw [this]
  ring

lemma dterm_nonneg (η r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hr0 : 0 < r) (hr1 : r < 1) (i : ℕ) :
    0 ≤ dterm η r i := by
  rw [dterm_eq η r hr0 hr1]
  obtain ⟨hk0, hk1⟩ := kap_bounds r hr0 hr1
  apply mul_nonneg
  · have : r ^ (i + 1) ≤ r ^ i := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    linarith
  · exact phi_nonneg η _ _ hη0 hη1 hk0.le (pow_nonneg hr0.le _) (pow_le_one₀ hr0.le hr1.le)

/-- `J(κ) ≤ Σ dterm ≤ J(κ)/r` -/
lemma L_bounds (η r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (dterm η r) ∧ J η (kap r) ≤ ∑' i, dterm η r i ∧
      ∑' i, dterm η r i ≤ J η (kap r) / r := by
  obtain ⟨hk0, hk1⟩ := kap_bounds r hr0 hr1
  set k := kap r
  have hpow : ∀ j : ℕ, 0 ≤ r ^ j ∧ r ^ j ≤ 1 := fun j =>
    ⟨pow_nonneg hr0.le _, pow_le_one₀ hr0.le hr1.le⟩
  have hle : ∀ j : ℕ, r ^ (j + 1) ≤ r ^ j := fun j => pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  -- each term is between the integrals
  have hlo : ∀ i, ∫ x in r ^ (i + 1)..r ^ i, phi η k x ≤ dterm η r i := by
    intro i
    rw [dterm_eq η r hr0 hr1]
    exact (int_bounds η k _ _ hη0 hη1 hk0.le hk1 (hpow _).1 (hle i) (hpow i).2).2
  have hhi : ∀ i, dterm η r i ≤ (1 / r) * ∫ x in r ^ (i + 2)..r ^ (i + 1), phi η k x := by
    intro i
    rw [dterm_eq η r hr0 hr1]
    have h := (int_bounds η k _ _ hη0 hη1 hk0.le hk1 (hpow _).1 (hle (i + 1)) (hpow (i + 1)).2).1
    have : r ^ i - r ^ (i + 1) = (1 / r) * (r ^ (i + 1) - r ^ (i + 1 + 1)) := by
      field_simp; ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hJ := fun n => small_int η k (r ^ n) hη0 hη1 hk0.le hk1 (hpow n).1 (hpow n).2
  have hpart : ∀ n, ∑ i ∈ Finset.range n, dterm η r i ≤ J η k / r := by
    intro n
    have h1 : ∑ i ∈ Finset.range n, dterm η r i ≤
        (1 / r) * ∑ i ∈ Finset.range n, ∫ x in r ^ (i + 2)..r ^ (i + 1), phi η k x := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun i _ => hhi i)
    have h2 : ∑ i ∈ Finset.range n, ∫ x in r ^ (i + 2)..r ^ (i + 1), phi η k x ≤
        ∑ i ∈ Finset.range (n + 1), ∫ x in r ^ (i + 1)..r ^ i, phi η k x := by
      rw [Finset.sum_range_succ']
      have : 0 ≤ ∫ x in r ^ (0 + 1)..r ^ 0, phi η k x := by
        apply intervalIntegral.integral_nonneg (hle 0)
        intro x hx
        exact phi_nonneg η k x hη0 hη1 hk0.le (le_trans (hpow _).1 hx.1) (le_trans hx.2 (hpow 0).2)
      linarith
    rw [tele η k r hη0 hη1 hk0.le hr0 hr1] at h2
    have h3 := (hJ (n + 1)).1
    calc ∑ i ∈ Finset.range n, dterm η r i ≤ (1 / r) * (J η k - ∫ x in (0:ℝ)..r ^ (n + 1), phi η k x) := by
          refine le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ ≤ J η k / r := by
          rw [show J η k / r = (1 / r) * J η k by ring]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsum : Summable (dterm η r) :=
    summable_of_sum_range_le (fun i => dterm_nonneg η r hη0 hη1 hr0 hr1 i) hpart
  refine ⟨hsum, ?_, hsum.tsum_le_of_sum_range_le hpart⟩
  -- lower bound: J - r^n / c ≤ partial sums ≤ tsum
  have hlow : ∀ n, J η k - r ^ n * (1 / (1 / η - 1)) ≤ ∑' i, dterm η r i := by
    intro n
    have h1 : ∑ i ∈ Finset.range n, ∫ x in r ^ (i + 1)..r ^ i, phi η k x ≤
        ∑ i ∈ Finset.range n, dterm η r i := Finset.sum_le_sum (fun i _ => hlo i)
    rw [tele η k r hη0 hη1 hk0.le hr0 hr1] at h1
    have h2 := hsum.sum_le_tsum (Finset.range n) (fun i _ => dterm_nonneg η r hη0 hη1 hr0 hr1 i)
    have h3 := (hJ n).2
    linarith
  have hlim : Tendsto (fun n : ℕ => J η k - r ^ n * (1 / (1 / η - 1))) atTop
      (𝓝 (J η k - 0 * (1 / (1 / η - 1)))) :=
    tendsto_const_nhds.sub ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const _)
  rw [zero_mul, sub_zero] at hlim
  exact le_of_tendsto' hlim hlow

/-- `J(k) → J(1)` as `k → 1`: `J(1) ≤ J(k) ≤ J(1) + (1 - k)/c²` -/
lemma J_close (η k : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    J η 1 ≤ J η k ∧ J η k ≤ J η 1 + (1 - k) * (1 / (1 / η - 1)) ^ 2 := by
  have hc := c_pos η hη0 hη1
  have hi : ∀ k', 0 ≤ k' → IntervalIntegrable (phi η k') volume 0 1 := fun k' hk' =>
    int_intble η k' 0 1 hη0 hη1 hk' le_rfl le_rfl zero_le_one zero_le_one
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1, phi η 1 x ≤ phi η k x ∧
      phi η k x ≤ phi η 1 x + (1 - k) * (1 / (1 / η - 1)) ^ 2 := by
    intro x hx
    have hl := Real.log_nonpos hx.1 hx.2
    have hA := psi_nonneg k x hk0 hx.1 hx.2
    have hB := psi_nonneg 1 x zero_le_one hx.1 hx.2
    set dk := x * (1 - k * Real.log x) + 1 / η - 1
    set d1 := x * (1 - 1 * Real.log x) + 1 / η - 1
    have hdk : 1 / η - 1 ≤ dk := by simp only [dk]; linarith
    have hd1 : 1 / η - 1 ≤ d1 := by simp only [d1]; linarith
    have hkd : dk ≤ d1 := by
      simp only [dk, d1]; nlinarith [mul_nonneg hx.1 (neg_nonneg.2 hl)]
    unfold phi
    constructor
    · exact one_div_le_one_div_of_le (by linarith) hkd
    · -- 1/dk - 1/d1 = (d1 - dk)/(dk d1) ≤ (1-k)/c²
      have hxl : |Real.log x * x| ≤ 1 := by
        rcases hx.1.eq_or_lt with h | h
        · subst h; simp
        · exact (Real.abs_log_mul_self_lt x h hx.2).le
      have hdiff : d1 - dk = (1 - k) * (-(Real.log x * x)) := by simp only [d1, dk]; ring
      have hdd : d1 - dk ≤ 1 - k := by
        rw [hdiff]
        have : -(Real.log x * x) ≤ 1 := by
          have := neg_abs_le (Real.log x * x); have := le_abs_self (-(Real.log x * x))
          rw [abs_neg] at this; linarith
        nlinarith
      have hdkp : 0 < dk := by linarith
      have hd1p : 0 < d1 := by linarith
      have : 1 / dk - 1 / d1 = (d1 - dk) / (dk * d1) := by field_simp
      have h2 : (d1 - dk) / (dk * d1) ≤ (1 - k) * (1 / (1 / η - 1)) ^ 2 := by
        rw [div_le_iff₀ (mul_pos hdkp hd1p)]
        have : (1 / η - 1) ^ 2 ≤ dk * d1 := by nlinarith
        have h3 : (1 - k) * (1 / (1 / η - 1)) ^ 2 * (1 / η - 1) ^ 2 = 1 - k := by
          rw [one_div_pow, mul_assoc, one_div_mul_cancel (pow_ne_zero 2 hc.ne'), mul_one]
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity :
          (0:ℝ) ≤ (1 - k) * (1 / (1 / η - 1)) ^ 2)]
      linarith
  unfold J
  constructor
  · exact intervalIntegral.integral_mono_on zero_le_one (hi 1 zero_le_one) (hi k hk0)
      (fun x hx => (hpt x hx).1)
  · have := intervalIntegral.integral_mono_on zero_le_one (hi k hk0)
      ((hi 1 zero_le_one).add intervalIntegrable_const) (fun x hx => (hpt x hx).2)
    rw [intervalIntegral.integral_add (hi 1 zero_le_one) intervalIntegrable_const,
      intervalIntegral.integral_const] at this
    simpa using this

lemma kap_tendsto : Tendsto kap (𝓝[<] 1) (𝓝 1) := by
  have hs := (Real.hasDerivAt_log (one_ne_zero)).tendsto_slope
  have hs' : Tendsto (slope Real.log 1) (𝓝[<] 1) (𝓝 1) := by
    have := hs.mono_left (nhdsWithin_mono _ fun x (hx : x ∈ Set.Iio 1) => (ne_of_lt hx : x ≠ 1))
    rwa [inv_one] at this
  have hinv := hs'.inv₀ one_ne_zero
  rw [inv_one] at hinv
  refine hinv.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with r hr
  unfold kap
  rw [slope_def_field, Real.log_one, sub_zero]
  have : r - 1 ≠ 0 := by linarith [hr.2]
  have hl : Real.log r ≠ 0 := (Real.log_neg hr.1 hr.2).ne
  field_simp
  ring

/-- the Riemann sum converges: `Σ dterm(r) → J(1)` as `r → 1⁻` -/
lemma L_tendsto (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    Tendsto (fun r => ∑' i, dterm η r i) (𝓝[<] 1) (𝓝 (J η 1)) := by
  have hev : ∀ᶠ r in 𝓝[<] (1:ℝ), r ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  -- J(κ r) → J(1)
  have hJk : Tendsto (fun r => J η (kap r)) (𝓝[<] 1) (𝓝 (J η 1)) := by
    have hup : Tendsto (fun r => J η 1 + (1 - kap r) * (1 / (1 / η - 1)) ^ 2) (𝓝[<] 1)
        (𝓝 (J η 1 + (1 - 1) * (1 / (1 / η - 1)) ^ 2)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.sub kap_tendsto).mul_const _)
    rw [sub_self, zero_mul, add_zero] at hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [hev] with r hr
      obtain ⟨hk0, hk1⟩ := kap_bounds r hr.1 hr.2
      exact (J_close η (kap r) hη0 hη1 hk0.le hk1).1
    · filter_upwards [hev] with r hr
      obtain ⟨hk0, hk1⟩ := kap_bounds r hr.1 hr.2
      exact (J_close η (kap r) hη0 hη1 hk0.le hk1).2
  have hJk' : Tendsto (fun r => J η (kap r) / r) (𝓝[<] 1) (𝓝 (J η 1 / 1)) :=
    hJk.div (tendsto_id.mono_left nhdsWithin_le_nhds) one_ne_zero
  rw [div_one] at hJk'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hJk hJk'
  · filter_upwards [hev] with r hr
    exact (L_bounds η r hη0 hη1 hr.1 hr.2).2.1
  · filter_upwards [hev] with r hr
    exact (L_bounds η r hη0 hη1 hr.1 hr.2).2.2

noncomputable def bb (r : ℝ) (i : ℕ) : ℝ := ((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)

lemma bb_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ℕ) : 0 ≤ bb p i := by
  unfold bb
  have h : ((i : ℝ) + 2) * p ^ (i + 1) - ((i : ℝ) + 1) * p ^ (i + 2)
      = p ^ (i + 1) * (((i : ℝ) + 2) - ((i : ℝ) + 1) * p) := by ring
  rw [h]
  apply mul_nonneg (pow_nonneg hp0 _)
  have : ((i : ℝ) + 1) * p ≤ (i : ℝ) + 1 := by
    have : (0:ℝ) ≤ (i : ℝ) + 1 := by positivity
    nlinarith
  linarith

lemma bb_le_one (p : ℝ) (hp0 : 0 ≤ p) (i : ℕ) : bb p i ≤ 1 := by
  unfold bb
  induction i with
  | zero =>
    simp
    nlinarith [sq_nonneg (p - 1)]
  | succ n ih =>
    have key : (((n + 1 : ℕ) : ℝ) + 2) * p ^ (n + 1 + 1) - (((n + 1 : ℕ) : ℝ) + 1) * p ^ (n + 1 + 2)
        = (((n : ℝ) + 2) * p ^ (n + 1) - ((n : ℝ) + 1) * p ^ (n + 2))
          - ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by
      push_cast; ring
    rw [key]
    have : 0 ≤ ((n : ℝ) + 2) * p ^ (n + 1) * (1 - p) ^ 2 := by positivity
    linarith

noncomputable def termN (η r : ℝ) (i : ℕ) : ℝ :=
  Real.log (1 - η + η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2))) /
    (((i : ℝ) + 1) * ((i : ℝ) + 2))

lemma summable_w : Summable (fun i : ℕ => 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  have h2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h2
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma termN_bound (η r : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : ℕ) :
    ‖termN η r i‖ ≤ (-Real.log (1 - η)) * (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) := by
  have h0 := bb_nonneg r hr0 hr1 i
  have h1 := bb_le_one r hr0 i
  unfold bb at h0 h1
  have hpos : 0 < 1 - η := by linarith
  set x := 1 - η + η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2))
  have hlo : 1 - η ≤ x := by simp only [x]; nlinarith
  have hhi : x ≤ 1 := by simp only [x]; nlinarith
  have hx0 : 0 < x := by linarith
  have hlogle : Real.log x ≤ 0 := Real.log_nonpos hx0.le hhi
  have hloglo : Real.log (1 - η) ≤ Real.log x := Real.log_le_log hpos hlo
  have hd : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  unfold termN
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd, abs_of_nonpos hlogle, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma termN_hasDeriv (η r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hr0 : 0 < r) (hr1 : r < 1) (i : ℕ) :
    HasDerivAt (fun r => termN η r i) (dterm η r i) r := by
  have hc := c_pos η hη0 hη1
  have h0 := bb_nonneg r hr0.le hr1.le i
  unfold bb at h0
  have hargpos : 0 < 1 - η + η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)) := by
    nlinarith
  have hb : HasDerivAt (fun r : ℝ => 1 - η + η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)))
      (η * (((i : ℝ) + 2) * (((i + 1 : ℕ) : ℝ) * r ^ (i + 1 - 1)) -
        ((i : ℝ) + 1) * (((i + 2 : ℕ) : ℝ) * r ^ (i + 2 - 1)))) r := by
    apply HasDerivAt.const_add
    apply HasDerivAt.const_mul
    apply HasDerivAt.sub
    · exact (hasDerivAt_pow (i + 1) r).const_mul _
    · exact (hasDerivAt_pow (i + 2) r).const_mul _
  have hl := (hb.log hargpos.ne').div_const ((((i : ℝ) + 1) * ((i : ℝ) + 2)))
  unfold termN
  refine hl.congr_deriv ?_
  unfold dterm
  have e1 : i + 1 - 1 = i := by omega
  have e2 : i + 2 - 1 = i + 1 := by omega
  rw [e1, e2]
  have hden : 0 < ((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2) + 1 / η - 1 := by
    linarith
  have hη' : η ≠ 0 := hη0.ne'
  have harg : 1 - η + η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2)) =
      η * (((i : ℝ) + 2) * r ^ (i + 1) - ((i : ℝ) + 1) * r ^ (i + 2) + 1 / η - 1) := by
    field_simp; ring
  rw [harg]
  push_cast
  field_simp
  ring

lemma N_hasDeriv (η r : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun r => ∑' i, termN η r i) (∑' i, dterm η r i) r := by
  have hc := c_pos η hη0 hη1
  set q := (1 + r) / 2
  have hq0 : 0 < q := by simp only [q]; linarith
  have hq1 : q < 1 := by simp only [q]; linarith
  have hrq : r < q := by simp only [q]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := fun i => q ^ i * (1 / (1 / η - 1)))
    (g := fun i r => termN η r i) (g' := fun i r => dterm η r i)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_right _) isOpen_Ioo isPreconnected_Ioo
    (t := Set.Ioo 0 q) (y₀ := r) ?_ ?_ ?_ ?_ ?_
  · intro i y hy
    exact termN_hasDeriv η y hη0 hη1 hy.1 (hy.2.trans hq1) i
  · intro i y hy
    have h0 := bb_nonneg y hy.1.le (hy.2.trans hq1).le i
    unfold bb at h0
    unfold dterm
    have hden : 1 / η - 1 ≤ ((i : ℝ) + 2) * y ^ (i + 1) - ((i : ℝ) + 1) * y ^ (i + 2) + 1 / η - 1 := by
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (pow_nonneg hy.1.le _)
      (by linarith [hy.2, hq1])) (by linarith))]
    rw [div_eq_mul_one_div]
    apply mul_le_mul _ (one_div_le_one_div_of_le hc hden) (one_div_nonneg.2 (by linarith))
      (pow_nonneg hq0.le _)
    have : y ^ i ≤ q ^ i := pow_le_pow_left₀ hy.1.le hy.2.le i
    have : y ^ i * (1 - y) ≤ y ^ i := by
      have := pow_nonneg hy.1.le i
      nlinarith [hy.1]
    linarith
  · exact ⟨hr0, hrq⟩
  · exact Summable.of_norm_bounded (summable_w.mul_left _)
      (fun i => termN_bound η r hη0.le hη1 hr0.le hr1.le i)
  · exact ⟨hr0, hrq⟩

lemma N_tendsto (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    Tendsto (fun r => ∑' i, termN η r i) (𝓝[<] 1) (𝓝 0) := by
  have hcont : ContinuousOn (fun r => ∑' i, termN η r i) (Set.Icc 0 1) := by
    apply continuousOn_tsum (u := fun i : ℕ => (-Real.log (1 - η)) *
        (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)))) _ (summable_w.mul_left _)
    · intro i r hr
      exact termN_bound η r hη0.le hη1 hr.1 hr.2 i
    · intro i
      unfold termN
      apply ContinuousOn.div_const
      apply ContinuousOn.log (by fun_prop)
      intro r hr
      have h0 := bb_nonneg r hr.1 hr.2 i
      unfold bb at h0
      have : 0 < 1 - η := by linarith
      nlinarith
  have h1 : (∑' i, termN η 1 i) = 0 := by
    have : ∀ i, termN η 1 i = 0 := by
      intro i
      unfold termN
      have : (1:ℝ) - η + η * (((i:ℝ) + 2) * 1 ^ (i + 1) - ((i:ℝ) + 1) * 1 ^ (i + 2)) = 1 := by
        simp only [one_pow, mul_one]; ring
      rw [this, Real.log_one, zero_div]
    simp [this]
  have hw := (hcont 1 ⟨zero_le_one, le_rfl⟩).tendsto
  simp only [h1] at hw
  rw [← nhdsWithin_Ioo_eq_nhdsLT (show (0:ℝ) < 1 by norm_num)]
  exact hw.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)

lemma D_hasDeriv (η r : ℝ) (hr0 : 0 < r) :
    HasDerivAt (fun r => Real.log r + η * (1 - r) ^ 2 / r) ((r - η * (1 - r ^ 2)) / r ^ 2) r := by
  have h1 := Real.hasDerivAt_log hr0.ne'
  have h2 := ((((hasDerivAt_id' r).const_sub 1).pow 2).const_mul η).div (hasDerivAt_id' r) hr0.ne'
  have h := h1.add h2
  refine h.congr_deriv ?_
  norm_num
  field_simp
  ring

end B8Aux

open B8Aux in
theorem solution (η : ℝ) (hη : η ∈ Set.Ioo (0:ℝ) 1) :
    Tendsto (fun p => SampleDrivenOS.Limit.hFun p η) (𝓝[<] 1)
      (𝓝 (∫ y in (0:ℝ)..1, 1 / (y * (1 - Real.log y) + 1 / η - 1))) := by
  obtain ⟨hη0, hη1⟩ := hη
  have hI : (∫ y in (0:ℝ)..1, 1 / (y * (1 - Real.log y) + 1 / η - 1)) = J η 1 := by
    unfold J phi; simp
  rw [hI]
  have hev : ∀ᶠ r in 𝓝[<] (1:ℝ), r ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hfun : (fun p => SampleDrivenOS.Limit.hFun p η) =
      fun p => (∑' i, termN η p i) / (Real.log p + η * (1 - p) ^ 2 / p) := by
    funext p; rfl
  rw [hfun]
  have hD'lim : Tendsto (fun r : ℝ => (r - η * (1 - r ^ 2)) / r ^ 2) (𝓝[<] 1) (𝓝 1) := by
    have : ContinuousAt (fun r : ℝ => (r - η * (1 - r ^ 2)) / r ^ 2) 1 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have h := this.tendsto
    simp only [one_pow, sub_self, mul_zero, sub_zero, div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_nhdsLT (f' := fun r => ∑' i, dterm η r i)
    (g' := fun r => (r - η * (1 - r ^ 2)) / r ^ 2)
  · filter_upwards [hev] with r hr
    exact N_hasDeriv η r hη0 hη1 hr.1 hr.2
  · filter_upwards [hev] with r hr
    exact D_hasDeriv η r hr.1
  · filter_upwards [hD'lim.eventually (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with r hr
    exact hr.ne'
  · exact N_tendsto η hη0 hη1
  · have : ContinuousAt (fun r : ℝ => Real.log r + η * (1 - r) ^ 2 / r) 1 := by
      apply ContinuousAt.add (Real.continuousAt_log one_ne_zero)
      apply ContinuousAt.div (by fun_prop) continuousAt_id one_ne_zero
    have h := this.tendsto
    simp only [Real.log_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, div_one, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · have := (L_tendsto η hη0 hη1).div hD'lim one_ne_zero
    rwa [div_one] at this
