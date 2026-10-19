-- Prove2me | solution 1 for RamanujanNotebooks.entry_39_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:47:27.025897+00:00
-- url     : https://prove2.me/submissions/0d313b4e-6952-4fea-9194-5aee9683afd7

import Mathlib

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

noncomputable def w (n k : ℕ) : ℝ := (-1 : ℝ) ^ k * (n.choose k : ℝ)
noncomputable def m (n k : ℕ) : ℝ := (n : ℝ) - 2 * k

noncomputable def G (n j : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), w n k * m n k ^ j * Real.cos (m n k * x - n * π / 2 + j * π / 2)

lemma term (n k : ℕ) (hk : k ≤ n) (x : ℝ) :
    (-Complex.I) ^ n * ((-Complex.exp (-(x * Complex.I))) ^ k * Complex.exp (x * Complex.I) ^ (n - k)
      * (n.choose k : ℂ))
    = ((w n k : ℝ) : ℂ) * Complex.exp (((m n k * x - n * π / 2 : ℝ) : ℂ) * Complex.I) := by
  have hI : -Complex.I = Complex.exp (-(π / 2 * Complex.I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  rw [hI, neg_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  simp only [w, m]
  push_cast
  have e : (((n - k : ℕ) : ℂ)) = (n : ℂ) - k := by rw [Nat.cast_sub hk]
  rw [e]
  have : Complex.exp (↑n * -(↑π / 2 * Complex.I)) *
      ((-1) ^ k * Complex.exp (↑k * -(↑x * Complex.I)) * Complex.exp ((↑n - ↑k) * (↑x * Complex.I))
        * ↑(n.choose k))
      = (-1) ^ k * ↑(n.choose k) * (Complex.exp (↑n * -(↑π / 2 * Complex.I)) *
          Complex.exp (↑k * -(↑x * Complex.I)) * Complex.exp ((↑n - ↑k) * (↑x * Complex.I))) := by ring
  rw [this, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

lemma sin_pow (n : ℕ) (x : ℝ) : (2 : ℝ) ^ n * Real.sin x ^ n = G n 0 x := by
  have hs : (2 * Complex.I * (Real.sin x : ℂ)) =
      -Complex.exp (-(x * Complex.I)) + Complex.exp (x * Complex.I) := by
    rw [Complex.ofReal_sin, Complex.sin]
    ring_nf
    rw [Complex.I_sq]; ring
  have key : (((2 : ℝ) ^ n * Real.sin x ^ n : ℝ) : ℂ) = (-Complex.I) ^ n * (2 * Complex.I * Real.sin x) ^ n := by
    push_cast
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring_nf
    rw [Complex.I_sq]; ring
  rw [hs, add_pow, Finset.mul_sum] at key
  have key2 : (((2 : ℝ) ^ n * Real.sin x ^ n : ℝ) : ℂ) =
      ∑ k ∈ range (n + 1), ((w n k : ℝ) : ℂ) *
        Complex.exp (((m n k * x - n * π / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [key]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    exact term n k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) x
  have := congrArg Complex.re key2
  rw [Complex.ofReal_re] at this
  rw [this, Complex.re_sum]
  unfold G
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp

lemma hasDerivAt_G (n j : ℕ) (x : ℝ) : HasDerivAt (G n j) (G n (j + 1) x) x := by
  unfold G
  have : ∀ k ∈ range (n + 1), HasDerivAt
      (fun x => w n k * m n k ^ j * Real.cos (m n k * x - n * π / 2 + j * π / 2))
      (w n k * m n k ^ (j + 1) * Real.cos (m n k * x - n * π / 2 + ((j + 1 : ℕ) : ℝ) * π / 2)) x := by
    intro k _
    have h1 : HasDerivAt (fun x => m n k * x - n * π / 2 + j * π / 2) (m n k) x := by
      simpa using ((hasDerivAt_id x).const_mul (m n k)).sub_const (n * π / 2) |>.add_const (j * π / 2)
    have h2 := (h1.cos).const_mul (w n k * m n k ^ j)
    refine h2.congr_deriv ?_
    have : m n k * x - n * π / 2 + ((j + 1 : ℕ) : ℝ) * π / 2
        = (m n k * x - n * π / 2 + j * π / 2) + π / 2 := by push_cast; ring
    rw [this, Real.cos_add_pi_div_two]
    ring
  have h := HasDerivAt.fun_sum this
  exact h

lemma moment (n j : ℕ) (hj : j < n) : ∑ k ∈ range (n + 1), w n k * m n k ^ j = 0 := by
  have h := fwdDiff_iter_eq_sum_shift (h := (1 : ℝ)) (fun r : ℝ => r ^ j) n (-(n : ℝ) / 2)
  rw [fwdDiff_iter_pow_eq_zero_of_lt hj] at h
  simp only [Pi.zero_apply, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h
  have : ∑ k ∈ range (n + 1), w n k * m n k ^ j =
      (-2) ^ j * (-1) ^ n * ∑ k ∈ range (n + 1),
        (((-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) : ℤ) : ℝ) * (-(n : ℝ) / 2 + k) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp only [w, m]
    push_cast
    have e1 : (-1 : ℝ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
    have e2 : ((-1 : ℝ) ^ (n - k)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [show (n : ℝ) - 2 * k = (-2) * (-(n : ℝ) / 2 + k) by ring, mul_pow, e1]
    linear_combination (-(-2 : ℝ) ^ j * (-1) ^ k * (n.choose k : ℝ) * (-(n : ℝ) / 2 + k) ^ j) * e2
  rw [this, ← h]; ring


lemma G_zero (n j : ℕ) (hj : j < n) : G n j 0 = 0 := by
  unfold G
  have : ∀ k ∈ range (n + 1), w n k * m n k ^ j * Real.cos (m n k * 0 - n * π / 2 + j * π / 2)
      = Real.cos (- n * π / 2 + j * π / 2) * (w n k * m n k ^ j) := by
    intro k _; rw [mul_zero, zero_sub, neg_mul, neg_div]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, moment n j hj, mul_zero]

lemma G_top (n : ℕ) (x : ℝ) : G n n x = ∑ k ∈ range (n + 1), w n k * m n k ^ n * Real.cos (m n k * x) := by
  unfold G
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 2; ring

noncomputable def Bd (n j : ℕ) : ℝ := ∑ k ∈ range (n + 1), |w n k * m n k ^ j|

lemma G_bound (n j : ℕ) (x : ℝ) : |G n j x| ≤ Bd n j := by
  unfold G Bd
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

lemma G_cont (n j : ℕ) : Continuous (G n j) :=
  continuous_iff_continuousAt.2 (fun x => (hasDerivAt_G n j x).continuousAt)

lemma exp_integrable (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun x => Real.exp (-t * x)) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 ht
  simpa [neg_mul] using this

lemma integrable_exp_mul (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Continuous f) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) : IntegrableOn (fun x => Real.exp (-t * x) * f x) (Ioi 0) := by
  refine Integrable.mul_bdd (c := B) (exp_integrable t ht) hf.aestronglyMeasurable.restrict ?_
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hB x)

lemma laplace_cos (t a : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * Real.cos (a * x) = t / (t ^ 2 + a ^ 2) := by
  have hpos : 0 < t ^ 2 + a ^ 2 := by positivity
  let F : ℝ → ℝ := fun x => Real.exp (-t * x) * (a * Real.sin (a * x) - t * Real.cos (a * x)) / (t ^ 2 + a ^ 2)
  have hF : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (Real.exp (-t * x) * Real.cos (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => Real.exp (-t * x)) (Real.exp (-t * x) * (-t)) x := by
      simpa using ((hasDerivAt_id x).const_mul (-t)).exp
    have h2 : HasDerivAt (fun x => a * Real.sin (a * x) - t * Real.cos (a * x))
        (a * (Real.cos (a * x) * a) - t * (-Real.sin (a * x) * a)) x := by
      have hs : HasDerivAt (fun x => Real.sin (a * x)) (Real.cos (a * x) * a) x := by
        simpa using ((hasDerivAt_id x).const_mul a).sin
      have hc : HasDerivAt (fun x => Real.cos (a * x)) (-Real.sin (a * x) * a) x := by
        simpa using ((hasDerivAt_id x).const_mul a).cos
      exact (hs.const_mul a).sub (hc.const_mul t)
    have := (h1.mul h2).div_const (t ^ 2 + a ^ 2)
    refine this.congr_deriv ?_
    field_simp
    ring
  have hint : IntegrableOn (fun x => Real.exp (-t * x) * Real.cos (a * x)) (Ioi 0) :=
    integrable_exp_mul t ht _ (by fun_prop) 1 (fun x => Real.abs_cos_le_one _)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have he : Tendsto (fun x => Real.exp (-t * x)) atTop (𝓝 0) := by
      have : Tendsto (fun x => -t * x) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp this
    have hb : ∀ x, |(a * Real.sin (a * x) - t * Real.cos (a * x)) / (t ^ 2 + a ^ 2)| ≤ (|a| + |t|) / (t ^ 2 + a ^ 2) := by
      intro x
      rw [abs_div, abs_of_pos hpos]
      gcongr
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    have := he.zero_mul_isBoundedUnder_le (g := fun x => (a * Real.sin (a * x) - t * Real.cos (a * x)) / (t ^ 2 + a ^ 2))
      ⟨(|a| + |t|) / (t ^ 2 + a ^ 2), Filter.eventually_map.2 (Filter.Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using hb x))⟩
    refine this.congr (fun x => ?_)
    simp only [F, Pi.mul_apply]; ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hF hint hlim]
  simp only [F, mul_zero, Real.sin_zero, Real.cos_zero, Real.exp_zero]
  field_simp
  ring

lemma laplace_ibp (n j : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n (j + 1) x
      = t * (∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n j x) - G n j 0 := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => Real.exp (-t * x)) (Real.exp (-t * x) * (-t)) x := by
    intro x _; simpa using ((hasDerivAt_id x).const_mul (-t)).exp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (G n j) (G n (j + 1) x) x := fun x _ => hasDerivAt_G n j x
  have h1 : IntegrableOn ((fun x => Real.exp (-t * x)) * G n (j + 1)) (Ioi 0) :=
    integrable_exp_mul t ht _ (G_cont n (j + 1)) _ (G_bound n (j + 1))
  have h2 : IntegrableOn ((fun x => Real.exp (-t * x) * (-t)) * G n j) (Ioi 0) := by
    have := (integrable_exp_mul t ht _ (G_cont n j) _ (G_bound n j)).const_mul (-t)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have hz : Tendsto ((fun x => Real.exp (-t * x)) * G n j) (𝓝[>] 0) (𝓝 (Real.exp (-t * 0) * G n j 0)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((Continuous.continuousAt (by fun_prop)).mul (G_cont n j).continuousAt)
  have hinf : Tendsto ((fun x => Real.exp (-t * x)) * G n j) atTop (𝓝 0) := by
    have he : Tendsto (fun x => Real.exp (-t * x)) atTop (𝓝 0) := by
      have : Tendsto (fun x => -t * x) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp this
    exact he.zero_mul_isBoundedUnder_le ⟨Bd n j, Filter.eventually_map.2
      (Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using G_bound n j x))⟩
  have := integral_Ioi_mul_deriv_eq_deriv_mul hu hv h1 h2 hz hinf
  have e : ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * (-t) * G n j x
      = -t * ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n j x := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [this, e, mul_zero, Real.exp_zero, one_mul]; ring

lemma laplace_G0 (n : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ n * ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n 0 x
      = ∑ k ∈ range (n + 1), w n k * m n k ^ n * (t / (t ^ 2 + m n k ^ 2)) := by
  have step : ∀ j ≤ n, t ^ j * ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n 0 x
      = ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n j x := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [laplace_ibp n j t ht, G_zero n j (by omega), ← ih (by omega)]; ring
  rw [step n le_rfl]
  simp_rw [G_top, Finset.mul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← laplace_cos t (m n k) ht, ← integral_const_mul]
    congr 1; ext x; ring
  · intro k _
    have := (integrable_exp_mul t ht _ (by fun_prop : Continuous fun x => Real.cos (m n k * x)) 1
      (fun x => Real.abs_cos_le_one _)).const_mul (w n k * m n k ^ n)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    ring

end RN39

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

lemma gamma_int (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-(x * t)) = ((n - 1).factorial : ℝ) / x ^ n := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ)) (r := x) (by exact_mod_cast hn) hx
  have e1 : ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) - 1) * Real.exp (-(x * t))
      = ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-(x * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [show (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hn]; simp, Real.rpow_natCast]
  rw [← e1, h]
  have e2 : Real.Gamma n = ((n - 1).factorial : ℝ) := by
    rw [show (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 by rw [Nat.cast_sub hn]; simp, Real.Gamma_nat_eq_factorial]
  rw [e2, Real.rpow_natCast, one_div, inv_pow]
  field_simp

lemma gamma_integrable (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t => t ^ (n - 1) * Real.exp (-(x * t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_int n hn x hx]
  have : (0 : ℝ) < ((n - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

lemma sinc_pow_integrable (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun x => |Real.sin x| ^ n / x ^ n) (Ioi 0) := by
  have hcont : ContinuousOn (fun x => |Real.sin x| ^ n / x ^ n) (Ioi 0) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx; exact pow_ne_zero _ (ne_of_gt hx)
  have hb1 : ∀ x ∈ Ioi (0 : ℝ), |Real.sin x| ^ n / x ^ n ≤ 1 := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    rw [div_le_one (by positivity)]
    apply pow_le_pow_left₀ (abs_nonneg _)
    have := Real.abs_sin_le_abs (x := x)
    rwa [abs_of_pos hx'] at this
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.of_bound (by simp) ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) 1 ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have h0 : 0 ≤ |Real.sin x| ^ n / x ^ n := by
      have : (0 : ℝ) < x := hx.1
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hb1 x hx.1
  · have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
    refine hi.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : (0 : ℝ) < x := by linarith
    have h0 : 0 ≤ |Real.sin x| ^ n / x ^ n := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.rpow_neg hx0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    calc |Real.sin x| ^ n / x ^ n ≤ 1 / x ^ n := by
          gcongr; exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)
      _ ≤ 1 / x ^ 2 := by
          gcongr
          exact hx1.le
      _ = (x ^ 2)⁻¹ := one_div _

lemma inv_sq_add_integral (a : ℝ) (ha : a ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2 + a ^ 2)⁻¹ = π / (2 * |a|) := by
  have hb : 0 < |a| := abs_pos.2 ha
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => (t ^ 2 + a ^ 2)⁻¹) 0 hb
  simp only [mul_zero] at h
  have e : ∫ x in Ioi (0 : ℝ), ((|a| * x) ^ 2 + a ^ 2)⁻¹ = (a ^ 2)⁻¹ * (π / 2) := by
    have h0 : ∫ x in Ioi (0 : ℝ), (1 + x ^ 2)⁻¹ = π / 2 := by simp
    rw [← h0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [mul_pow, sq_abs]
    field_simp
    ring
  rw [e, smul_eq_mul] at h
  have : ∫ x in Ioi (0 : ℝ), (x ^ 2 + a ^ 2)⁻¹ = |a| * ((a ^ 2)⁻¹ * (π / 2)) := by
    rw [h]; field_simp
  rw [this, ← sq_abs a]
  field_simp

lemma inv_sq_add_integrable (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun t : ℝ => (t ^ 2 + a ^ 2)⁻¹) := by
  have := (integrable_inv_one_add_sq.comp_div ha).const_mul ((a ^ 2)⁻¹)
  refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only
  field_simp
  ring

end RN39

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

noncomputable def c (n k : ℕ) : ℝ :=
  if m n k = 0 then 0 else w n k * m n k ^ n * (π / (2 * |m n k|))

noncomputable def F (n : ℕ) (x t : ℝ) : ℝ := t ^ (n - 1) * Real.exp (-(x * t)) * Real.sin x ^ n

lemma inner_t (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), F n x t = ((n - 1).factorial : ℝ) * (Real.sin x ^ n / x ^ n) := by
  unfold F
  rw [integral_mul_const, gamma_int n hn x hx]
  ring

lemma inner_t_norm (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), ‖F n x t‖ = ((n - 1).factorial : ℝ) * (|Real.sin x| ^ n / x ^ n) := by
  have : ∫ t in Ioi (0 : ℝ), ‖F n x t‖
      = ∫ t in Ioi (0 : ℝ), t ^ (n - 1) * Real.exp (-(x * t)) * |Real.sin x| ^ n := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    unfold F
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), abs_of_pos ht']
  rw [this, integral_mul_const, gamma_int n hn x hx]
  ring

lemma F_integrable (n : ℕ) (hn : 2 ≤ n) :
    Integrable (Function.uncurry (F n)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hc : Continuous (Function.uncurry (F n)) := by
    unfold F Function.uncurry; fun_prop
  rw [integrable_prod_iff hc.aestronglyMeasurable]
  constructor
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun x hx => ?_))
    have := (gamma_integrable n (by omega) x hx).mul_const (Real.sin x ^ n)
    simpa [Function.uncurry, F] using this
  · have := (sinc_pow_integrable n hn).const_mul ((n - 1).factorial : ℝ)
    refine IntegrableOn.congr_fun this (fun x hx => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    rw [inner_t_norm n (by omega) x hx]

lemma inner_x (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), F n x t = ∑ k ∈ range (n + 1), (2 ^ n)⁻¹ * (w n k * m n k ^ n * (t ^ 2 + m n k ^ 2)⁻¹) := by
  have h1 : ∫ x in Ioi (0 : ℝ), F n x t
      = t ^ (n - 1) * (2 ^ n)⁻¹ * ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n 0 x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    unfold F
    rw [← sin_pow n x, mul_comm x t, neg_mul]
    field_simp
  have h2 := laplace_G0 n t ht
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.ne'
  rw [h1, show (∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * G n 0 x)
      = (t ^ n)⁻¹ * ∑ k ∈ range (n + 1), w n k * m n k ^ n * (t / (t ^ 2 + m n k ^ 2)) by
    rw [← h2]; field_simp]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : t ^ (n - 1) * t = t ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hpos2 : 0 < t ^ 2 + m n k ^ 2 := by positivity
  field_simp
  rw [← this]; ring

lemma main_integral (n : ℕ) (hn : 2 ≤ n) :
    ∫ x in Ioi (0 : ℝ), Real.sin x ^ n / x ^ n
      = (2 ^ n)⁻¹ / ((n - 1).factorial : ℝ) * ∑ k ∈ range (n + 1), c n k := by
  have hfact : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h1 : ∫ x in Ioi (0 : ℝ), Real.sin x ^ n / x ^ n
      = ((n - 1).factorial : ℝ)⁻¹ * ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F n x t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [inner_t n (by omega) x hx]
    field_simp
  rw [h1, integral_integral_swap (F_integrable n hn)]
  have h2 : ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F n x t
      = ∫ t in Ioi (0 : ℝ), ∑ k ∈ range (n + 1), (2 ^ n)⁻¹ * (w n k * m n k ^ n * (t ^ 2 + m n k ^ 2)⁻¹) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => inner_x n (by omega) t ht)
  rw [h2, integral_finset_sum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, integral_const_mul]
    unfold c
    split_ifs with hm
    · rw [hm, zero_pow (by omega)]; simp
    · rw [inv_sq_add_integral _ hm]; field_simp
  · intro k _
    by_cases hm : m n k = 0
    · simp [hm, zero_pow (show n ≠ 0 by omega)]
    · exact ((inv_sq_add_integrable _ hm).const_mul _).const_mul _ |>.integrableOn

end RN39

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

lemma prod_eq (n k : ℕ) :
    (∏ j ∈ range k, (-(n : ℝ) + j)) = (-1) ^ k * (n.choose k : ℝ) * (k.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    have h := Nat.choose_succ_right_eq n k
    by_cases hk : k ≤ n
    · have h' : ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (n.choose k : ℝ) * ((n : ℝ) - k) := by
        have := congrArg (fun x : ℕ => (x : ℝ)) h
        push_cast [Nat.cast_sub hk] at this
        exact this
      push_cast
      linear_combination ((-1 : ℝ) ^ k * (k.factorial : ℝ)) * h'
    · push_neg at hk
      rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
      simp

lemma c_reflect (n k : ℕ) (hk : k ≤ n) : c n (n - k) = c n k := by
  have hm : m n (n - k) = -m n k := by
    unfold m; rw [Nat.cast_sub hk]; ring
  have hw : w n (n - k) = (-1) ^ n * w n k := by
    unfold w
    rw [Nat.choose_symm hk]
    have e1 : (-1 : ℝ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
    rw [e1]
    have e2 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (-(-1 : ℝ) ^ (n - k) * (n.choose k : ℝ)) * e2
  unfold c
  rw [hm, hw]
  by_cases h0 : m n k = 0
  · rw [if_pos (by rw [h0, neg_zero]), if_pos h0]
  · rw [if_neg (by rwa [neg_eq_zero]), if_neg h0, abs_neg, neg_pow]
    have e3 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination (w n k * m n k ^ n * (π / (2 * |m n k|))) * e3

lemma c_pos (n k : ℕ) (h : 2 * k < n) (hn : 1 ≤ n) : c n k = w n k * m n k ^ (n - 1) * (π / 2) := by
  have hm : 0 < m n k := by
    unfold m; have : (2 * k : ℝ) < n := by exact_mod_cast h
    linarith
  unfold c
  rw [if_neg hm.ne', abs_of_pos hm]
  have : m n k ^ n = m n k ^ (n - 1) * m n k := by rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [this]
  field_simp

lemma sum_fold (N : ℕ) :
    ∑ k ∈ range (N + 1 + 1), c (N + 1) k = 2 * ∑ k ∈ range (N / 2 + 1), w (N + 1) k * m (N + 1) k ^ N * (π / 2) := by
  set n := N + 1 with hn
  have split : ∀ k ∈ range (n + 1), c n k = (if 2 * k < n then c n k else 0) + (if n < 2 * k then c n k else 0) := by
    intro k _
    by_cases h1 : 2 * k < n
    · rw [if_pos h1, if_neg (by omega)]; ring
    · by_cases h2 : n < 2 * k
      · rw [if_neg h1, if_pos h2]; ring
      · have : m n k = 0 := by
          unfold m; have : (2 * k : ℝ) = n := by exact_mod_cast (by omega : 2 * k = n)
          linarith
        rw [if_neg h1, if_neg h2]; unfold c; rw [if_pos this]; ring
  rw [Finset.sum_congr rfl split, Finset.sum_add_distrib]
  have refl : ∑ k ∈ range (n + 1), (if n < 2 * k then c n k else 0)
      = ∑ k ∈ range (n + 1), (if 2 * k < n then c n k else 0) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [show n + 1 - 1 - j = n - j by omega]
    by_cases h : 2 * j < n
    · rw [if_pos h, if_pos (by omega), c_reflect n j hj']
    · rw [if_neg h, if_neg (by omega)]
  rw [refl, ← two_mul, ← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun k => 2 * k < n) = range (N / 2 + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [c_pos n k (by simp at hk; omega) (by omega), show n - 1 = N by omega]

end RN39

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

lemma sinc_sq_integrable : IntegrableOn (fun x => Real.sinc x ^ 2) (Ioi 0) := by
  refine IntegrableOn.congr_fun (sinc_pow_integrable 2 le_rfl) (fun x hx => ?_) measurableSet_Ioi
  have hx' : x ≠ 0 := ne_of_gt hx
  rw [Real.sinc_of_ne_zero hx', div_pow, sq_abs]

lemma sinc_sq_integral : ∫ x in Ioi (0 : ℝ), Real.sinc x ^ 2 = π / 2 := by
  have h := main_integral 2 le_rfl
  have hs := sum_fold 1
  norm_num at hs
  have e : ∫ x in Ioi (0 : ℝ), Real.sinc x ^ 2 = ∫ x in Ioi (0 : ℝ), Real.sin x ^ 2 / x ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Real.sinc_of_ne_zero (ne_of_gt hx), div_pow]
  rw [e, h, show (2 + 1 : ℕ) = 1 + 1 + 1 from rfl, hs]
  simp [w, m]
  ring

lemma R_hasDerivAt (T : ℝ) (hT : 0 < T) :
    HasDerivAt (fun T : ℝ => T / 2 * Real.sinc (T / 2) ^ 2)
      (Real.sin (T / 2) * Real.cos (T / 2) / (T / 2) - Real.sin (T / 2) ^ 2 / (2 * (T / 2) ^ 2)) T := by
  have hT2 : T / 2 ≠ 0 := by positivity
  have hg : HasDerivAt (fun T : ℝ => Real.sin (T / 2) ^ 2 / (T / 2))
      (Real.sin (T / 2) * Real.cos (T / 2) / (T / 2) - Real.sin (T / 2) ^ 2 / (2 * (T / 2) ^ 2)) T := by
    have h1 : HasDerivAt (fun T : ℝ => T / 2) (1 / 2) T := by
      simpa using (hasDerivAt_id T).div_const 2
    have h2 : HasDerivAt (fun T : ℝ => Real.sin (T / 2) ^ 2) (2 * Real.sin (T / 2) * (Real.cos (T / 2) * (1 / 2))) T := by
      have := (h1.sin).fun_pow 2
      simpa using this
    have := h2.div h1 hT2
    refine this.congr_deriv ?_
    field_simp
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hT] with x hx
  have hx2 : x / 2 ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx2]
  field_simp

lemma dirichlet_eq (T : ℝ) (hT : 0 < T) :
    ∫ x in (0 : ℝ)..T, Real.sinc x = (∫ x in (0 : ℝ)..T / 2, Real.sinc x ^ 2) + T / 2 * Real.sinc (T / 2) ^ 2 := by
  have hc2 : Continuous (fun x => Real.sinc x ^ 2) := Real.continuous_sinc.pow 2
  let f : ℝ → ℝ := fun T => (∫ x in (0 : ℝ)..T / 2, Real.sinc x ^ 2) + T / 2 * Real.sinc (T / 2) ^ 2
  have hfc : Continuous f := by
    have h1 : Continuous (fun s => ∫ x in (0 : ℝ)..s, Real.sinc x ^ 2) :=
      intervalIntegral.continuous_primitive (fun a b => hc2.intervalIntegrable a b) 0
    have h2 : Continuous (fun T : ℝ => T / 2 * Real.sinc (T / 2) ^ 2) := by
      have := Real.continuous_sinc
      fun_prop
    exact (h1.comp (continuous_id.div_const 2)).add h2
  have hd : ∀ x ∈ Ioo 0 T, HasDerivAt f (Real.sinc x) x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hQ0 : HasDerivAt (fun s => ∫ y in (0 : ℝ)..s, Real.sinc y ^ 2) (Real.sinc (x / 2) ^ 2) (x / 2) :=
      (hc2.integral_hasStrictDerivAt 0 (x / 2)).hasDerivAt
    have h1 : HasDerivAt (fun T : ℝ => T / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    have hQ := hQ0.comp x h1
    have := hQ.add (R_hasDerivAt x hx0)
    refine this.congr_deriv ?_
    have hx2 : x / 2 ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hx2, Real.sinc_of_ne_zero (ne_of_gt hx0)]
    have hs : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      rw [← Real.sin_two_mul]; ring_nf
    rw [hs]
    field_simp
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT.le hfc.continuousOn
    (fun x hx => (hd x hx).hasDerivWithinAt) (Real.continuous_sinc.intervalIntegrable 0 T)
  rw [this]
  simp [f]

lemma dirichlet : Tendsto (fun T => ∫ x in (0 : ℝ)..T, Real.sinc x) atTop (𝓝 (π / 2)) := by
  have hQ : Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T / 2, Real.sinc x ^ 2) atTop (𝓝 (π / 2)) := by
    rw [← sinc_sq_integral]
    exact intervalIntegral_tendsto_integral_Ioi 0 sinc_sq_integrable
      (tendsto_id.atTop_div_const two_pos)
  have hR : Tendsto (fun T : ℝ => T / 2 * Real.sinc (T / 2) ^ 2) atTop (𝓝 0) := by
    have hup : Tendsto (fun T : ℝ => 2 / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      positivity
    · filter_upwards [eventually_gt_atTop 0] with T hT
      have hT2 : T / 2 ≠ 0 := by positivity
      rw [Real.sinc_of_ne_zero hT2]
      have : Real.sin (T / 2) ^ 2 ≤ 1 := by
        have := Real.sin_sq_le_one (T / 2); linarith
      rw [div_pow]
      calc T / 2 * (Real.sin (T / 2) ^ 2 / (T / 2) ^ 2) = Real.sin (T / 2) ^ 2 / (T / 2) := by
            field_simp
        _ ≤ 1 / (T / 2) := by gcongr
        _ = 2 / T := by field_simp
  have := hQ.add hR
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [dirichlet_eq T hT]

end RN39

open Real Finset MeasureTheory Set Filter Topology

namespace RN39

lemma target_sum (N : ℕ) :
    ∑ k ∈ Finset.range (N / 2 + 1),
      (∏ j ∈ Finset.range k, (-((N : ℝ) + 1) + (j : ℝ))) / (k.factorial : ℝ) * (((N : ℝ) + 1) - 2 * (k : ℝ)) ^ N
    = ∑ k ∈ range (N / 2 + 1), w (N + 1) k * m (N + 1) k ^ N := by
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h := prod_eq (N + 1) k
  push_cast at h
  rw [h]
  have : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  simp only [w, m]
  push_cast
  field_simp

theorem main (N : ℕ) :
    Filter.Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x ^ (N + 1) / x ^ (N + 1))
      Filter.atTop
      (nhds (Real.pi / (2 ^ (N + 1) * (N.factorial : ℝ)) *
        ∑ k ∈ Finset.range (N / 2 + 1),
          (∏ j ∈ Finset.range k, (-((N : ℝ) + 1) + (j : ℝ))) / (k.factorial : ℝ)
            * (((N : ℝ) + 1) - 2 * (k : ℝ)) ^ N)) := by
  rw [target_sum]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have e : (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x ^ (0 + 1) / x ^ (0 + 1))
        = fun T => ∫ x in (0 : ℝ)..T, Real.sinc x := by
      ext T
      refine intervalIntegral.integral_congr_ae ?_
      have hae : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
      filter_upwards [hae] with x hx0 _
      rw [Real.sinc_of_ne_zero hx0]; simp
    rw [e]
    convert dirichlet using 2
    simp [w, m]
  · set n := N + 1 with hn
    have hint : IntegrableOn (fun x => Real.sin x ^ n / x ^ n) (Ioi 0) := by
      refine (sinc_pow_integrable n (by omega)).mono' ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro x hx; exact pow_ne_zero _ (ne_of_gt hx)
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun x hx => ?_))
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_pow, abs_of_pos (show (0 : ℝ) < x from hx)]
    have := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    rw [main_integral n (by omega), sum_fold N] at this
    have hv : Real.pi / (2 ^ (N + 1) * (N.factorial : ℝ)) * ∑ k ∈ range (N / 2 + 1), w (N + 1) k * m (N + 1) k ^ N
        = (2 ^ n)⁻¹ / ((n - 1).factorial : ℝ) *
          (2 * ∑ k ∈ Finset.range (N / 2 + 1), w (N + 1) k * m (N + 1) k ^ N * (π / 2)) := by
      rw [show n - 1 = N by omega, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
      rw [hn]
      field_simp
    rw [hv]; exact this

end RN39

theorem solution (N : ℕ) :
    Filter.Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, Real.sin x ^ (N + 1) / x ^ (N + 1))
      Filter.atTop
      (nhds (Real.pi / (2 ^ (N + 1) * (N.factorial : ℝ)) *
        ∑ k ∈ Finset.range (N / 2 + 1),
          (∏ j ∈ Finset.range k, (-((N : ℝ) + 1) + (j : ℝ))) / (k.factorial : ℝ)
            * (((N : ℝ) + 1) - 2 * (k : ℝ)) ^ N)) :=
  RN39.main N
