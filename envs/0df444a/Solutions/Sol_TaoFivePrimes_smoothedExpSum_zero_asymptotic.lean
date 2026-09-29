-- Prove2me | solution 1 for TaoFivePrimes.smoothedExpSum_zero_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T23:14:28.416096+00:00
-- url     : https://prove2.me/submissions/dc205b24-1695-4556-ae8d-3c1a95ee4fb6

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt
open TaoFivePrimes

namespace TaoL43b

theorem cont_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (deriv f) := by
  have := ContDiff.continuous_iteratedDeriv 1 hf (by exact_mod_cast le_top)
  simpa [iteratedDeriv_one] using this

/-- `ψ` written as a sum of indicators over a fixed range. -/
theorem psi_eq_indicator {x : ℝ} {N : ℕ} (hN : ⌊x⌋₊ ≤ N) {y : ℝ} (hy0 : 0 ≤ y) (hyx : y ≤ x) :
    Chebyshev.psi y = ∑ n ∈ Finset.Ioc 0 N, (if (n : ℝ) ≤ y then (Λ n : ℝ) else 0) := by
  classical
  have hset : Finset.Ioc 0 ⌊y⌋₊ = (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ℝ) ≤ y) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hn0, hnf⟩
      have hfy : ⌊y⌋₊ ≤ N := le_trans (Nat.floor_le_floor hyx) hN
      exact ⟨⟨hn0, le_trans hnf hfy⟩, (Nat.le_floor_iff hy0).mp hnf⟩
    · rintro ⟨⟨hn0, _⟩, hny⟩
      exact ⟨hn0, Nat.le_floor hny⟩
  rw [Chebyshev.psi, hset, Finset.sum_filter]

/-- `η` vanishes at the right endpoint of its support interval. -/
theorem eta_one_eq_zero {eta : ℝ → ℝ} (hcont : Continuous eta)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) : eta 1 = 0 := by
  have h1 : Filter.Tendsto eta (nhdsWithin 1 (Set.Ioi 1)) (nhds (eta 1)) :=
    hcont.continuousWithinAt
  have h0 : Filter.Tendsto eta (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hsupp t ht).symm
  exact tendsto_nhds_unique h1 h0

/-- The truncated integral of a continuous function. -/
theorem integral_indicator_split {f : ℝ → ℝ} (hf : Continuous f) {a x : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) :
    (∫ y in (0:ℝ)..x, (if a ≤ y then f y else 0)) = ∫ y in a..x, f y := by
  have hind : (fun y : ℝ => if a ≤ y then f y else 0) = Set.indicator (Set.Ici a) f := by
    funext y; rw [Set.indicator_apply]; simp [Set.mem_Ici]
  have hII : ∀ u v : ℝ, IntervalIntegrable (fun y : ℝ => if a ≤ y then f y else 0) volume u v := by
    intro u v
    rw [hind]
    exact ⟨(hf.integrableOn_Ioc).indicator measurableSet_Ici,
      (hf.integrableOn_Ioc).indicator measurableSet_Ici⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := (0:ℝ)) (b := a) (c := x)
    (hII 0 a) (hII a x)
  have hleft : (∫ y in (0:ℝ)..a, (if a ≤ y then f y else 0)) = 0 := by
    have hz : (∫ y in (0:ℝ)..a, (if a ≤ y then f y else 0)) = ∫ _y in (0:ℝ)..a, (0:ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton a)] with y hy hmem
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
      rw [Set.uIoc_of_le ha, Set.mem_Ioc] at hmem
      rw [if_neg (fun hcon => hy (le_antisymm hmem.2 hcon))]
    rw [hz]; simp
  have hright : (∫ y in a..x, (if a ≤ y then f y else 0)) = ∫ y in a..x, f y := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le hax, Set.mem_Icc] at hy
    rw [if_pos hy.1]
  rw [hleft, hright] at hsplit
  linarith [hsplit]


/-- **Abel summation in integral form.**  For a smooth cutoff supported in `[c,1]`,
`∑_{n ≤ x} Λ(n) η(n/x) = -∫_0^x ψ(y) η'(y/x) dy / x`. -/
theorem abel_psi {eta : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) {x : ℝ} (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) * eta ((n : ℝ) / x))
      = -∫ y in (0:ℝ)..x, Chebyshev.psi y * (deriv eta (y / x) / x) := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hcont : Continuous eta := hsm.continuous
  have hcd : Continuous (deriv eta) := cont_deriv hsm
  have hcdg : Continuous (fun y : ℝ => deriv eta (y / x) / x) := by fun_prop
  have hg : ∀ y : ℝ, HasDerivAt (fun t : ℝ => eta (t / x)) (deriv eta (y / x) / x) y := by
    intro y
    have hb : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
      simpa using (hasDerivAt_id y).div_const x
    have hgg : HasDerivAt eta (deriv eta (y / x)) (y / x) :=
      (hsm.differentiable (by simp) (y / x)).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => eta (t / x)) (deriv eta (y / x) * (1 / x)) y :=
      hgg.comp y hb
    have heq : deriv eta (y / x) * (1 / x) = deriv eta (y / x) / x := by ring
    rw [heq] at hcomp
    exact hcomp
  have h1 : eta 1 = 0 := eta_one_eq_zero hcont hsupp
  -- rewrite the integrand as a finite sum of truncated pieces
  have hcongr : (∫ y in (0:ℝ)..x, Chebyshev.psi y * (deriv eta (y / x) / x))
      = ∫ y in (0:ℝ)..x,
          ∑ n ∈ Finset.Ioc 0 N,
            (if (n : ℝ) ≤ y then (Λ n : ℝ) * (deriv eta (y / x) / x) else 0) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le (le_of_lt hx0), Set.mem_Icc] at hy
    rw [psi_eq_indicator (le_of_eq hNdef.symm) hy.1 hy.2, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : (n : ℝ) ≤ y
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [hcongr]
  have hII : ∀ (n : ℕ) (u v : ℝ),
      IntervalIntegrable
        (fun y : ℝ => if (n : ℝ) ≤ y then (Λ n : ℝ) * (deriv eta (y / x) / x) else 0)
        volume u v := by
    intro n u v
    have hf : Continuous (fun y : ℝ => (Λ n : ℝ) * (deriv eta (y / x) / x)) :=
      continuous_const.mul hcdg
    have hind : (fun y : ℝ => if (n : ℝ) ≤ y then (Λ n : ℝ) * (deriv eta (y / x) / x) else 0)
        = Set.indicator (Set.Ici (n : ℝ)) (fun y => (Λ n : ℝ) * (deriv eta (y / x) / x)) := by
      funext y; rw [Set.indicator_apply]; simp [Set.mem_Ici]
    rw [hind]
    exact ⟨(hf.integrableOn_Ioc).indicator measurableSet_Ici,
      (hf.integrableOn_Ioc).indicator measurableSet_Ici⟩
  rw [intervalIntegral.integral_finsetSum (fun n _ => hII n 0 x)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  simp only [Finset.mem_Ioc] at hn
  have hnx : (n : ℝ) ≤ x := by
    have := Nat.floor_le (le_of_lt hx0)
    rw [← hNdef] at this
    exact le_trans (by exact_mod_cast hn.2) this
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsp := integral_indicator_split (f := fun y : ℝ => (Λ n : ℝ) * (deriv eta (y / x) / x))
    (continuous_const.mul hcdg) hn0 hnx
  rw [hsp, intervalIntegral.integral_const_mul]
  have hftc : (∫ y in (n : ℝ)..x, deriv eta (y / x) / x) = eta (x / x) - eta ((n : ℝ) / x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hg y)
      (hcdg.intervalIntegrable _ _)
  rw [hftc, div_self (ne_of_gt hx0), h1, zero_sub]
  ring


/-- Rescaling an `L¹` integral: `∫ f(y/x) dy = x ∫ f` for `x > 0`. -/
theorem integral_rescale {f : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ, f (y / x)) = x * ∫ t : ℝ, f t := by
  have hEq : (fun y : ℝ => f (y / x)) = fun y : ℝ => f (x⁻¹ * y) := by
    funext y; rw [div_eq_inv_mul]
  rw [hEq, MeasureTheory.Measure.integral_comp_mul_left f x⁻¹, abs_of_pos (by positivity),
    inv_inv, smul_eq_mul]

/-- The integral over `[0,x]` of a function supported in `[0,x]` is the full integral. -/
theorem integral_full {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (hx : 0 < x)
    (hz : ∀ y : ℝ, y < 0 ∨ x < y → f y = 0) :
    (∫ y in (0:ℝ)..x, f y) = ∫ y : ℝ, f y := by
  have hz' : ∀ y ∈ (Set.Icc (0:ℝ) x)ᶜ, f y = 0 := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hy
    exact hz y hy
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hz',
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (le_of_lt hx)]

theorem main_term {eta : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) {x : ℝ} (hx : 1 ≤ x)
    (hsupp0 : ∀ t : ℝ, t < 0 → eta t = 0) (hsupp1 : ∀ t : ℝ, 1 < t → eta t = 0) :
    (∫ y in (0:ℝ)..x, y * (deriv eta (y / x) / x)) = -(x * ∫ t : ℝ, eta t) := by
  have hx0 : (0:ℝ) < x := by linarith
  have hcont : Continuous eta := hsm.continuous
  have hcd : Continuous (deriv eta) := cont_deriv hsm
  have hcdg : Continuous (fun y : ℝ => deriv eta (y / x) / x) := by fun_prop
  have h1 : eta 1 = 0 := eta_one_eq_zero hcont hsupp1
  have hg : ∀ y : ℝ, HasDerivAt (fun t : ℝ => eta (t / x)) (deriv eta (y / x) / x) y := by
    intro y
    have hb : HasDerivAt (fun t : ℝ => t / x) (1 / x) y := by
      simpa using (hasDerivAt_id y).div_const x
    have hgg : HasDerivAt eta (deriv eta (y / x)) (y / x) :=
      (hsm.differentiable (by simp) (y / x)).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => eta (t / x)) (deriv eta (y / x) * (1 / x)) y :=
      hgg.comp y hb
    have heq : deriv eta (y / x) * (1 / x) = deriv eta (y / x) / x := by ring
    rw [heq] at hcomp
    exact hcomp
  -- product rule
  have hprod : ∀ y : ℝ, HasDerivAt (fun t : ℝ => t * eta (t / x))
      (eta (y / x) + y * (deriv eta (y / x) / x)) y := by
    intro y
    have hid : HasDerivAt (fun t : ℝ => t) (1:ℝ) y := hasDerivAt_id' y
    have hm : HasDerivAt (fun t : ℝ => t * eta (t / x))
        (1 * eta (y / x) + y * (deriv eta (y / x) / x)) y := hid.mul (hg y)
    rwa [one_mul] at hm
  have hcp : Continuous (fun y : ℝ => eta (y / x) + y * (deriv eta (y / x) / x)) := by fun_prop
  have hftc : (∫ y in (0:ℝ)..x, (eta (y / x) + y * (deriv eta (y / x) / x)))
      = x * eta (x / x) - 0 * eta (0 / x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hprod y)
      (hcp.intervalIntegrable _ _)
  rw [div_self (ne_of_gt hx0), h1, mul_zero, zero_mul, sub_zero] at hftc
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun y : ℝ =>
      eta (y / x)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun y : ℝ => y * (deriv eta (y / x) / x)).intervalIntegrable _ _)]
    at hftc
  have hz : ∀ y : ℝ, y < 0 ∨ x < y → eta (y / x) = 0 := by
    intro y hy
    rcases hy with h | h
    · exact hsupp0 _ (div_neg_of_neg_of_pos h hx0)
    · exact hsupp1 _ (by rw [lt_div_iff₀ hx0, one_mul]; exact h)
  have hfull : (∫ y in (0:ℝ)..x, eta (y / x)) = ∫ y : ℝ, eta (y / x) :=
    integral_full (by fun_prop) hx0 hz
  rw [hfull, integral_rescale hx0] at hftc
  linarith [hftc]


theorem psi_mono : Monotone Chebyshev.psi := by
  intro a b hab
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor hab)) ?_
  intro i _ _
  exact ArithmeticFunction.vonMangoldt_nonneg

theorem deriv_zero_off {eta : ℝ → ℝ} {c t : ℝ}
    (hsupp : ∀ u : ℝ, u < c ∨ 1 < u → eta u = 0) (h : t < c ∨ 1 < t) : deriv eta t = 0 := by
  rcases h with h | h
  · have hev : eta =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Set.Iio c from h)] with u hu
      exact hsupp u (Or.inl hu)
    rw [hev.deriv_eq, deriv_const]
  · have hev : eta =ᶠ[nhds t] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Set.Ioi (1:ℝ) from h)] with u hu
      exact hsupp u (Or.inr hu)
    rw [hev.deriv_eq, deriv_const]

theorem error_term {eta : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) {c x L : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, t < c ∨ 1 < t → eta t = 0)
    (hpsi : ∀ y : ℝ, c * x ≤ y → y ≤ x → |Chebyshev.psi y - y| ≤ y / L) :
    |∫ y in (0:ℝ)..x, (Chebyshev.psi y - y) * (deriv eta (y / x) / x)|
      ≤ (x / L) * ∫ t : ℝ, |deriv eta t| := by
  have hx0 : (0:ℝ) < x := by linarith
  have hcd : Continuous (deriv eta) := cont_deriv hsm
  have hcdg : Continuous (fun y : ℝ => deriv eta (y / x) / x) := by fun_prop
  have hdgz : ∀ y : ℝ, y < c * x ∨ x < y → deriv eta (y / x) / x = 0 := by
    intro y hy
    have h : y / x < c ∨ 1 < y / x := by
      rcases hy with h | h
      · exact Or.inl (by rw [div_lt_iff₀ hx0]; linarith [h])
      · exact Or.inr (by rw [lt_div_iff₀ hx0, one_mul]; exact h)
    rw [deriv_zero_off hsupp h, zero_div]
  -- interval integrability of the step-function factor
  have hIIpsi : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y) volume 0 x := by
    refine IntervalIntegrable.sub ?_ (continuous_id.intervalIntegrable _ _)
    exact (psi_mono.monotoneOn _).intervalIntegrable
  have hII : IntervalIntegrable
      (fun y : ℝ => (Chebyshev.psi y - y) * (deriv eta (y / x) / x)) volume 0 x :=
    hIIpsi.mul_continuousOn hcdg.continuousOn
  have hIIabs : IntervalIntegrable
      (fun y : ℝ => |(Chebyshev.psi y - y) * (deriv eta (y / x) / x)|) volume 0 x := hII.abs
  have hIImaj : IntervalIntegrable
      (fun y : ℝ => (x / L) * |deriv eta (y / x) / x|) volume 0 x :=
    ((continuous_const.mul hcdg.abs).intervalIntegrable _ _)
  -- pointwise majorant
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) x,
      |(Chebyshev.psi y - y) * (deriv eta (y / x) / x)|
        ≤ (x / L) * |deriv eta (y / x) / x| := by
    intro y hy
    rcases lt_or_ge y (c * x) with h | h
    · rw [hdgz y (Or.inl h)]
      simp
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine le_trans (hpsi y h hy.2) ?_
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hy.2 (by positivity)
  calc |∫ y in (0:ℝ)..x, (Chebyshev.psi y - y) * (deriv eta (y / x) / x)|
      ≤ ∫ y in (0:ℝ)..x, |(Chebyshev.psi y - y) * (deriv eta (y / x) / x)| :=
        intervalIntegral.abs_integral_le_integral_abs (le_of_lt hx0)
    _ ≤ ∫ y in (0:ℝ)..x, (x / L) * |deriv eta (y / x) / x| :=
        intervalIntegral.integral_mono_on (le_of_lt hx0) hIIabs hIImaj hpt
    _ = (x / L) * ∫ t : ℝ, |deriv eta t| := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have hzz : ∀ y : ℝ, y < 0 ∨ x < y → |deriv eta (y / x) / x| = 0 := by
          intro y hy
          rcases hy with h | h
          · rw [hdgz y (Or.inl (by nlinarith)), abs_zero]
          · rw [hdgz y (Or.inr h), abs_zero]
        rw [integral_full (by fun_prop) hx0 hzz]
        have habs : ∀ y : ℝ, |deriv eta (y / x) / x| = |deriv eta (y / x)| / x := by
          intro y; rw [abs_div, abs_of_pos hx0]
        simp only [habs]
        rw [MeasureTheory.integral_div, integral_rescale (f := fun t => |deriv eta t|) hx0]
        field_simp


theorem smoothedExpSum_zero_eq {eta : ℝ → ℝ} {x : ℝ} (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    smoothedExpSum eta 1 x 0
      = (((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) * eta ((n : ℝ) / x) : ℝ)) : ℂ) := by
  classical
  have hx0 : (0:ℝ) < x := by linarith
  have hvanish : ∀ n : ℕ, n ∉ Finset.Ioc 0 ⌊x⌋₊ →
      (if Nat.Coprime n 1 then (Λ n : ℂ) * expCircle (0 * n) * (eta ((n : ℝ) / x) : ℂ) else 0)
        = 0 := by
    intro n hn
    simp only [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hn
    rw [if_pos (Nat.coprime_one_right n)]
    rcases hn with h | h
    · have : n = 0 := by omega
      subst this
      simp
    · have hgt : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h
      have h2 := Nat.lt_floor_add_one x
      have : eta ((n : ℝ) / x) = 0 := by
        refine hsupp _ ?_
        rw [lt_div_iff₀ hx0, one_mul]
        linarith
      rw [this]
      simp
  rw [smoothedExpSum, tsum_eq_sum hvanish, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [if_pos (Nat.coprime_one_right n)]
  simp [expCircle]

/-- **Tao, Lemma 4.3, equation (4.4).**  For a smooth cutoff supported in `[c,1]`,
`S_{η,1}(x,0) = x ∫η + O*( ‖η'‖_{L¹} x / (40 log cx) )`, given the Rosser–Schoenfeld
bound `ψ(y) = y + O*(y / (40 log cx))` on `[cx, x]`. -/
theorem rs_lemma_smooth {eta : ℝ → ℝ} (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) {c x : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, t < c ∨ 1 < t → eta t = 0)
    (hcx : (10:ℝ) ^ 8 ≤ c * x)
    (hpsi : ∀ y : ℝ, c * x ≤ y → y ≤ x →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log (c * x))) :
    ‖smoothedExpSum eta 1 x 0 - (((∫ t : ℝ, eta t) * x : ℝ) : ℂ)‖
      ≤ 1 / (40 * Real.log (c * x)) * (∫ t : ℝ, |deriv eta t|) * x := by
  have hx0 : (0:ℝ) < x := by linarith
  have hsupp1 : ∀ t : ℝ, 1 < t → eta t = 0 := fun t h => hsupp t (Or.inr h)
  have hsupp0 : ∀ t : ℝ, t < 0 → eta t = 0 := fun t h => hsupp t (Or.inl (by linarith))
  set L : ℝ := 40 * Real.log (c * x) with hLdef
  have hlog : (0:ℝ) < Real.log (c * x) := by
    refine Real.log_pos ?_
    nlinarith
  have hL : (0:ℝ) < L := by rw [hLdef]; linarith
  have hcdg : Continuous (fun y : ℝ => deriv eta (y / x) / x) := by
    have := cont_deriv hsm; fun_prop
  -- Abel summation
  have hab := abel_psi hsm hx hsupp1
  -- split the integral
  have hIIpsi : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y) volume 0 x := by
    refine IntervalIntegrable.sub ?_ (continuous_id.intervalIntegrable _ _)
    exact (psi_mono.monotoneOn _).intervalIntegrable
  have hII1 : IntervalIntegrable
      (fun y : ℝ => (Chebyshev.psi y - y) * (deriv eta (y / x) / x)) volume 0 x :=
    hIIpsi.mul_continuousOn hcdg.continuousOn
  have hII2 : IntervalIntegrable (fun y : ℝ => y * (deriv eta (y / x) / x)) volume 0 x :=
    ((continuous_id.mul hcdg).intervalIntegrable _ _)
  have hsplit : (∫ y in (0:ℝ)..x, Chebyshev.psi y * (deriv eta (y / x) / x))
      = (∫ y in (0:ℝ)..x, (Chebyshev.psi y - y) * (deriv eta (y / x) / x))
        + ∫ y in (0:ℝ)..x, y * (deriv eta (y / x) / x) := by
    rw [← intervalIntegral.integral_add hII1 hII2]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    ring
  have hmain := main_term hsm hx hsupp0 hsupp1
  rw [hsplit, hmain] at hab
  -- the sum equals the main term minus the error integral
  have hval : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) * eta ((n : ℝ) / x))
      - (∫ t : ℝ, eta t) * x
      = -∫ y in (0:ℝ)..x, (Chebyshev.psi y - y) * (deriv eta (y / x) / x) := by
    rw [hab]; ring
  have herr := error_term hsm hc0 hc1 hx hL hsupp hpsi
  rw [smoothedExpSum_zero_eq hx hsupp1, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, hval, abs_neg]
  refine herr.trans_eq ?_
  rw [hLdef]
  ring




end TaoL43b

theorem solution (eta : ℝ → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) (c x : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, t < c ∨ 1 < t → eta t = 0)
    (hcx : (10 : ℝ) ^ 8 ≤ c * x)
    (hpsi : ∀ y : ℝ, c * x ≤ y → y ≤ x →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log (c * x))) :
    ‖TaoFivePrimes.smoothedExpSum eta 1 x 0 - (((∫ t : ℝ, eta t) * x : ℝ) : ℂ)‖
      ≤ 1 / (40 * Real.log (c * x)) * (∫ t : ℝ, |deriv eta t|) * x :=
  TaoL43b.rs_lemma_smooth hsm hc0 hc1 hx hsupp hcx hpsi
