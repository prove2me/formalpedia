-- Prove2me | solution 2 for TaoFivePrimes.reciprocal_primes_theta_tail_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T11:36:50.645977+00:00
-- url     : https://prove2.me/submissions/196d19d0-21a3-405d-92b7-9885afdccc58

import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem
import Theorems.Thm_TaoFivePrimes_reciprocal_prime_mertens_limit

set_option autoImplicit false

namespace R42ThetaTail

open Real Filter Topology MeasureTheory

/-- `log t ^ 4 ≤ 4096 √t` for `t ≥ 1`. -/
lemma log_pow_four_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 4 ≤ 4096 * Real.sqrt t := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : Real.log t ≤ t ^ ((1:ℝ)/8) / (1/8) := Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2 : (t ^ ((1:ℝ)/8)) ^ 4 = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc Real.log t ^ 4 ≤ (t ^ ((1:ℝ)/8) / (1/8)) ^ 4 := by gcongr
    _ = 4096 * (t ^ ((1:ℝ)/8)) ^ 4 := by ring
    _ = 4096 * Real.sqrt t := by rw [h2]

/-- `log t ^ 3 ≤ 27 t` for `t ≥ 1`. -/
lemma log_pow_three_le {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 3 ≤ 27 * t := by
  have h0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : Real.log t ≤ t ^ ((1:ℝ)/3) / (1/3) := Real.log_le_rpow_div (by linarith) (by norm_num)
  have h2 : (t ^ ((1:ℝ)/3)) ^ 3 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  calc Real.log t ^ 3 ≤ (t ^ ((1:ℝ)/3) / (1/3)) ^ 3 := by gcongr
    _ = 27 * (t ^ ((1:ℝ)/3)) ^ 3 := by ring
    _ = 27 * t := by rw [h2]

/-- From the PNT with error `X (log X)^(-3)` for `ψ` on naturals: `|θ t - t| log³ t ≤ K t`. -/
lemma theta_err
    (hpsi : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      |(∑ n ∈ Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n) - (X : ℝ)| ≤
        C * ((X : ℝ) * Real.log X ^ (-A))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t →
      |Chebyshev.theta t - t| * Real.log t ^ 3 ≤ K * t := by
  obtain ⟨C, hC⟩ := hpsi 3 (by norm_num)
  refine ⟨8192 + 8 * |C| + 27, by positivity, fun t ht => ?_⟩
  have hn2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hnt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htn : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have hn2r : (2:ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hn2
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hLn : 0 < Real.log ⌊t⌋₊ := Real.log_pos (by linarith)
  have hsq : t ≤ (⌊t⌋₊ : ℝ) ^ 2 := by nlinarith
  have hLL : Real.log t ≤ 2 * Real.log ⌊t⌋₊ := by
    have := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hpsi_t : Chebyshev.psi t =
      ∑ k ∈ Finset.Ioc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt k := rfl
  have h1 := hC ⌊t⌋₊ hn2
  rw [← hpsi_t] at h1
  have hrp : Real.log ⌊t⌋₊ ^ (-(3:ℝ)) = (Real.log ⌊t⌋₊ ^ 3)⁻¹ := by
    rw [Real.rpow_neg hLn.le]; norm_cast
  rw [hrp] at h1
  have e1 : |Chebyshev.psi t - ⌊t⌋₊| * Real.log t ^ 3 ≤ 8 * |C| * t := by
    have hpos : 0 ≤ (⌊t⌋₊ : ℝ) * (Real.log ⌊t⌋₊ ^ 3)⁻¹ := by positivity
    have : |Chebyshev.psi t - ⌊t⌋₊| ≤ |C| * ((⌊t⌋₊ : ℝ) * (Real.log ⌊t⌋₊ ^ 3)⁻¹) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hpos)
    calc |Chebyshev.psi t - ⌊t⌋₊| * Real.log t ^ 3
        ≤ |C| * ((⌊t⌋₊ : ℝ) * (Real.log ⌊t⌋₊ ^ 3)⁻¹) * (2 * Real.log ⌊t⌋₊) ^ 3 := by
          gcongr
      _ = 8 * |C| * ⌊t⌋₊ := by field_simp; ring
      _ ≤ 8 * |C| * t := by gcongr
  have e2 : |Chebyshev.theta t - Chebyshev.psi t| * Real.log t ^ 3 ≤ 8192 * t := by
    have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := t) (by linarith)
    rw [abs_sub_comm] at h
    have h4 := log_pow_four_le (t := t) (by linarith)
    have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
    calc |Chebyshev.theta t - Chebyshev.psi t| * Real.log t ^ 3
        ≤ 2 * Real.sqrt t * Real.log t * Real.log t ^ 3 := by gcongr
      _ = 2 * Real.sqrt t * Real.log t ^ 4 := by ring
      _ ≤ 2 * Real.sqrt t * (4096 * Real.sqrt t) := by gcongr
      _ = 8192 * (Real.sqrt t * Real.sqrt t) := by ring
      _ = 8192 * t := by rw [hs]
  have e3 : |(⌊t⌋₊ : ℝ) - t| * Real.log t ^ 3 ≤ 27 * t := by
    have : |(⌊t⌋₊ : ℝ) - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have h3 := log_pow_three_le (t := t) (by linarith)
    calc |(⌊t⌋₊ : ℝ) - t| * Real.log t ^ 3 ≤ 1 * Real.log t ^ 3 := by gcongr
      _ ≤ 27 * t := by linarith
  have tri : |Chebyshev.theta t - t| ≤ |Chebyshev.theta t - Chebyshev.psi t|
      + |Chebyshev.psi t - ⌊t⌋₊| + |(⌊t⌋₊ : ℝ) - t| := by
    calc |Chebyshev.theta t - t| = |(Chebyshev.theta t - Chebyshev.psi t)
          + (Chebyshev.psi t - ⌊t⌋₊) + ((⌊t⌋₊ : ℝ) - t)| := by ring_nf
      _ ≤ _ := abs_add_three _ _ _
  have hL3 : 0 ≤ Real.log t ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right tri hL3
  rw [add_mul, add_mul] at this
  linarith

/-- `1 / (t log⁴ t)` is integrable on `(2, ∞)`. -/
lemma integrableOn_inv_mul_log_pow_four :
    IntegrableOn (fun t : ℝ => (t * Real.log t ^ 4)⁻¹) (Set.Ioi 2) := by
  have hderiv : ∀ x ∈ Set.Ioi (2:ℝ), HasDerivAt (fun t => -(1/3) * (Real.log t ^ 3)⁻¹)
      ((x * Real.log x ^ 4)⁻¹) x := by
    intro x hx
    have hx2 : (2:ℝ) < x := hx
    have hx0 : x ≠ 0 := by linarith
    have hL : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
    have h : HasDerivAt (fun t => -(1/3) * (Real.log t ^ 3)⁻¹)
        (-(1 / 3) * (-(((3:ℕ):ℝ) * Real.log x ^ (3 - 1) * x⁻¹) / (Real.log x ^ 3) ^ 2)) x :=
      (((Real.hasDerivAt_log hx0).pow 3).inv (pow_ne_zero 3 hL)).const_mul (-(1/3:ℝ))
    refine h.congr_deriv ?_
    simp only [show (3:ℕ) - 1 = 2 from rfl, Nat.cast_ofNat]
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg (g := fun t => -(1/3) * (Real.log t ^ 3)⁻¹) (l := 0)
    ?_ hderiv ?_ ?_
  · have hL : Real.log 2 ^ 3 ≠ 0 := pow_ne_zero 3 (Real.log_pos (by norm_num)).ne'
    have : ContinuousAt (fun t : ℝ => -(1/3) * (Real.log t ^ 3)⁻¹) 2 :=
      continuousAt_const.mul (((Real.continuousAt_log (by norm_num)).pow 3).inv₀ hL)
    exact this.continuousWithinAt
  · intro x hx
    have hx2 : (2:ℝ) < x := hx
    have : 0 < x := by linarith
    have : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  · have : Tendsto (fun t => (Real.log t ^ 3)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp Real.tendsto_log_atTop)
    simpa using this.const_mul (-(1/3:ℝ))

/-- The integrand `(θ t - t)(log t + 1)/(t² log² t)`. -/
noncomputable def g (t : ℝ) : ℝ :=
  (Chebyshev.theta t - t) * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

lemma measurable_g : Measurable g := by
  have hm : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  unfold g
  fun_prop

lemma integrableOn_g (K : ℝ) (_hK : 0 ≤ K)
    (hθ : ∀ t : ℝ, 2 ≤ t → |Chebyshev.theta t - t| * Real.log t ^ 3 ≤ K * t) :
    IntegrableOn g (Set.Ioi 2) := by
  have hb : IntegrableOn (fun t : ℝ => 3 * K * (t * Real.log t ^ 4)⁻¹) (Set.Ioi 2) :=
    integrableOn_inv_mul_log_pow_four.const_mul (3 * K)
  refine hb.mono' measurable_g.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : (2:ℝ) < t := ht
  have ht0 : 0 < t := by linarith
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hL2 : Real.log 2 < Real.log t := Real.log_lt_log (by norm_num) ht2
  have hl2 := Real.log_two_gt_d9
  have h3 : Real.log t + 1 ≤ 3 * Real.log t := by linarith
  have hE := hθ t ht2.le
  set E := |Chebyshev.theta t - t| with hEdef
  have hE0 : 0 ≤ E := abs_nonneg _
  unfold g
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by linarith : 0 < Real.log t + 1),
    abs_of_pos (by positivity : 0 < t ^ 2 * Real.log t ^ 2), ← hEdef,
    div_le_iff₀ (by positivity)]
  have hR : 3 * K * (t * Real.log t ^ 4)⁻¹ * (t ^ 2 * Real.log t ^ 2) = 3 * K * t / Real.log t ^ 2 := by
    field_simp
  rw [hR, le_div_iff₀ (by positivity)]
  have hEL : 0 ≤ E * Real.log t ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hEL]

/-- Derivative of `1/(t log t)`. -/
lemma hasDerivAt_f {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun x : ℝ => (x * Real.log x)⁻¹)
      (-(Real.log u + 1) / (u * Real.log u) ^ 2) u := by
  have hu0 : u ≠ 0 := by linarith
  have hL : Real.log u ≠ 0 := (Real.log_pos hu).ne'
  exact (Real.hasDerivAt_mul_log hu0).inv (mul_ne_zero hu0 hL)

set_option backward.isDefEq.respectTransparency.types false in
/-- Abel summation: `∑_{p ≤ x} 1/p = θ(x)/(x log x) + ∫₂ˣ θ(t)(log t + 1)/(t² log² t) dt`. -/
lemma abel_reciprocal (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) =
      Chebyshev.theta x / (x * Real.log x) +
        ∫ t in (2:ℝ)..x, Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) := by
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ Real.log n)
  have ha : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, a k = Chebyshev.theta t := by
    intro t
    simp [a, Set.indicator_apply, Finset.sum_filter, Chebyshev.theta_eq_sum_Icc]
  have hsum : ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ) =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (fun t : ℝ => (t * Real.log t)⁻¹) n * a n := by
    rw [Nat.primesLE_eq_filter_Icc_zero, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n.Prime
    · have hl : Real.log n ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (mod_cast h.pos) (mod_cast h.ne_one)
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
      simp only [a, h, if_true, Set.indicator_apply]
      simp [h]
      field_simp
    · simp [a, h]
  rw [hsum, sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ => (t * Real.log t)⁻¹)
    (by simp [a]) (by simp [a]) x ?diff ?int, ← intervalIntegral.integral_of_le hx, ha]
  · have hcongr : ∫ t in (2:ℝ)..x, deriv (fun t : ℝ => (t * Real.log t)⁻¹) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, a k =
        ∫ t in (2:ℝ)..x, -(Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hx] at ht
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : t ≠ 0 := by linarith
      have hL : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
      rw [(hasDerivAt_f ht1).deriv, ha]
      field_simp
    rw [hcongr, intervalIntegral.integral_neg]
    simp only [sub_neg_eq_add]
    rw [div_eq_mul_inv, mul_comm]
  case diff =>
    intro t ht
    exact (hasDerivAt_f (by linarith [ht.1])).differentiableAt
  case int =>
    have hc : ContinuousOn (fun t : ℝ => -(Real.log t + 1) / (t * Real.log t) ^ 2) (Set.Icc 2 x) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      have hne : (t * Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero ht0 hL)
      exact (((Real.continuousAt_log ht0).add continuousAt_const).neg.div
        ((continuousAt_id.mul (Real.continuousAt_log ht0)).pow 2) hne).continuousWithinAt
    refine (hc.congr fun t ht => ?_).integrableOn_Icc
    exact (hasDerivAt_f (by linarith [ht.1])).deriv

/-- `∫₂ˣ (log t + 1)/(t log² t) dt = [log log t - 1/log t]₂ˣ`. -/
lemma integral_main (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * Real.log t ^ 2) =
      (Real.log (Real.log x) - (Real.log x)⁻¹) - (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
  have hd : ∀ t ∈ Set.uIcc (2:ℝ) x, HasDerivAt (fun t => Real.log (Real.log t) - (Real.log t)⁻¹)
      ((Real.log t + 1) / (t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h1 : HasDerivAt (fun t => Real.log (Real.log t) - (Real.log t)⁻¹)
        (t⁻¹ / Real.log t - -t⁻¹ / Real.log t ^ 2) t :=
      ((Real.hasDerivAt_log h0).log hL).sub ((Real.hasDerivAt_log h0).inv hL)
    refine h1.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ?_]
  refine ContinuousOn.intervalIntegrable ?_
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  have h0 : t ≠ 0 := by linarith [ht.1]
  have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
  have hne : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero h0 (pow_ne_zero 2 hL)
  exact (((Real.continuousAt_log h0).add continuousAt_const).div
    (continuousAt_id.mul ((Real.continuousAt_log h0).pow 2)) hne).continuousWithinAt

/-- The finite identity behind the Mertens constant. -/
lemma finite_identity (x : ℝ) (hx : 2 ≤ x) (hint : IntervalIntegrable g volume 2 x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) =
      1 / Real.log 2 - Real.log (Real.log 2) +
        (Chebyshev.theta x - x) / (x * Real.log x) + ∫ t in (2:ℝ)..x, g t := by
  have hcont : IntervalIntegrable (fun t : ℝ => (Real.log t + 1) / (t * Real.log t ^ 2)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hne : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero h0 (pow_ne_zero 2 hL)
    exact (((Real.continuousAt_log h0).add continuousAt_const).div
      (continuousAt_id.mul ((Real.continuousAt_log h0).pow 2)) hne).continuousWithinAt
  have hsplit : ∫ t in (2:ℝ)..x, Chebyshev.theta t * (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) =
      (∫ t in (2:ℝ)..x, g t) + ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_add hint hcont]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [g]
    field_simp
    ring
  rw [abel_reciprocal x hx, hsplit, integral_main x hx]
  have h0 : x ≠ 0 := by linarith
  have hL : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hL2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp
  ring

/-- The main theorem, from the two platform inputs (PNT for `ψ` with a `(log X)^(-A)` error, and
Mertens' theorem with the exact constant). -/
theorem main_of
    (hpsi : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      |(∑ n ∈ Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n) - (X : ℝ)| ≤
        C * ((X : ℝ) * Real.log X ^ (-A)))
    (hmert : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x))
      atTop (nhds (Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))))) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
        (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) (Set.Ioi (2 : ℝ)) ∧
    (Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) =
      1 / Real.log 2 - Real.log (Real.log 2) +
      ∫ t in Set.Ioi (2 : ℝ),
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  simp only [← Chebyshev.theta_eq_sum_primesLE]
  change IntegrableOn g (Set.Ioi 2) ∧ _ = _ + ∫ t in Set.Ioi (2:ℝ), g t
  obtain ⟨K, hK, hθ⟩ := theta_err hpsi
  have hint := integrableOn_g K hK hθ
  refine ⟨hint, ?_⟩
  have h1 : Tendsto (fun x : ℝ => (Chebyshev.theta x - x) / (x * Real.log x)) atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => K * (Real.log x ^ 4)⁻¹) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by norm_num : (4:ℕ) ≠ 0)).comp Real.tendsto_log_atTop)).const_mul K
      simpa using this
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hx0 : 0 < x := by linarith
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    have hE := hθ x hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < x * Real.log x),
      div_le_iff₀ (by positivity)]
    have hR : K * (Real.log x ^ 4)⁻¹ * (x * Real.log x) = K * x / Real.log x ^ 3 := by
      field_simp
    rw [hR, le_div_iff₀ (by positivity)]
    exact hE
  have h2 : Tendsto (fun x : ℝ => ∫ t in (2:ℝ)..x, g t) atTop (𝓝 (∫ t in Set.Ioi (2:ℝ), g t)) :=
    intervalIntegral_tendsto_integral_Ioi 2 hint tendsto_id
  have h3 := ((tendsto_const_nhds (x := 1 / Real.log 2 - Real.log (Real.log 2))).add h1).add h2
  rw [add_zero] at h3
  have hlim : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x)) atTop
      (𝓝 (1 / Real.log 2 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2:ℝ), g t)) := by
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hii : IntervalIntegrable g volume 2 x :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
        (hint.mono_set Set.Ioc_subset_Ioi_self)
    rw [finite_identity x hx hii]
  exact tendsto_nhds_unique hmert hlim


/-- The tail identity, from the same two platform inputs. -/
theorem tail_of
    (hpsi : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ X : ℕ, 2 ≤ X →
      |(∑ n ∈ Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n) - (X : ℝ)| ≤
        C * ((X : ℝ) * Real.log X ^ (-A)))
    (hmert : Tendsto (fun x : ℝ =>
      (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x))
      atTop (nhds (Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))))
    (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x) / (x * Real.log x) -
      ∫ t in Set.Ioi x,
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  obtain ⟨K, hK, hθ⟩ := theta_err hpsi
  have hint := integrableOn_g K hK hθ
  have hB0 := (main_of hpsi hmert).2
  simp only [← Chebyshev.theta_eq_sum_primesLE] at hB0 ⊢
  change _ = _ + ∫ t in Set.Ioi (2:ℝ), g t at hB0
  change _ = _ + _ + _ - ∫ t in Set.Ioi x, g t
  have hii : IntervalIntegrable g volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (hint.mono_set Set.Ioc_subset_Ioi_self)
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hii
    (hint.mono_set (Set.Ioi_subset_Ioi hx))
  have hfi := finite_identity x hx hii
  rw [hB0, ← hsplit]
  linarith [hfi]

end R42ThetaTail

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x) / (x * Real.log x) -
      ∫ t in Set.Ioi x,
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  exact R42ThetaTail.tail_of ArtinPrimitiveRoots.psi_prime_number_theorem
    TaoFivePrimes.reciprocal_prime_mertens_limit x hx
