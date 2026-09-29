-- Prove2me | solution 1 for ProbabilisticNT.turan_kubilius
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T03:12:44.998722+00:00
-- url     : https://prove2.me/submissions/f3d02b41-f9c4-48cf-9e6d-c93fed199ee4

import Mathlib

set_option maxHeartbeats 1000000
set_option linter.all false

-- ==== upstream: Salt/Maynard/Mertens.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# N3.2 — Mertens' second theorem, upper bound

`Σ_{p ≤ x} 1/p ≤ log log x + C`.  mathlib has no Mertens theorems, so this
is built from the von Mangoldt convolution + Chebyshev's `ψ`-bound + Abel
summation.  Only the UPPER direction is needed downstream (N3.4 → N5.2).

Route (see the node brief):
* **Step 1** `Σ_{n≤N} log n ≤ N log N`.
* **Step 2** divisor swap `Σ_{n≤N} log n = Σ_{d≤N} Λ d · ⌊N/d⌋`.
* **Step 3/4** ⇒ `Σ_{p≤N} (log p)/p ≤ log N + c`  (Mertens' 1st, upper).
* **Step 5** Abel summation against the weight `1/log t` ⇒ the log-log bound.
-/

open Finset ArithmeticFunction

namespace Salt.Maynard

/-! ## Step 2 — the divisor swap -/

/-- For `0 < n ≤ N`, the divisors of `n` are exactly the elements of
`Ioc 0 N` dividing `n`. -/
theorem divisors_eq_filter_Ioc {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    n.divisors = (Finset.Ioc 0 N).filter (· ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hd, _⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    have hdn : d ≤ n := Nat.le_of_dvd hn hd
    exact ⟨⟨hdpos, hdn.trans hnN⟩, hd⟩
  · rintro ⟨⟨_, _⟩, hd⟩
    exact ⟨hd, hn.ne'⟩

/-- **Step 2.** `Σ_{n=1}^{N} log n = Σ_{d=1}^{N} Λ d · ⌊N/d⌋`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  -- rewrite each `log n` as `Σ_{d ∣ n} Λ d`, extended over `Ioc 0 N`
  have hstep : ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ n ∈ Finset.Ioc 0 N, ∑ d ∈ Finset.Ioc 0 N,
          (if d ∣ n then Λ d else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [← ArithmeticFunction.vonMangoldt_sum (n := n),
      divisors_eq_filter_Ioc hn.1 hn.2, Finset.sum_filter]
  rw [hstep, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  -- `Σ_n (if d ∣ n then Λ d else 0) = Λ d · #{n ∈ Ioc 0 N : d ∣ n} = Λ d · (N/d)`
  rw [← Finset.sum_filter, Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,
    nsmul_eq_mul, mul_comm]

/-! ## Step 1 — the log-sum upper bound -/

/-- **Step 1.** `Σ_{n=1}^{N} log n ≤ N · log N`. -/
theorem sum_log_le (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ (N : ℝ) * Real.log N := by
  have hle : ∑ n ∈ Finset.Ioc 0 N, Real.log n
      ≤ ∑ _n ∈ Finset.Ioc 0 N, Real.log N := by
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    apply Real.log_le_log (by exact_mod_cast hn.1)
    exact_mod_cast hn.2
  rw [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hle
  exact hle

/-! ## Steps 3 & 4 — Mertens' first theorem, upper bound -/

/-- `⌊N/d⌋ ≥ N/d − 1` as reals, for `0 < d`. -/
theorem cast_div_ge {N d : ℕ} (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := by
  have hdm := Nat.div_add_mod N d
  have hlt := Nat.mod_lt N hd
  have hnat : N ≤ d * (N / d) + d := by omega
  have hcast : (N : ℝ) ≤ (d : ℝ) * ((N / d : ℕ) : ℝ) + d := by exact_mod_cast hnat
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ hdr]
  nlinarith [hcast]

/-- `Σ_{d≤N} Λ d = ψ N`, packaged at a `Nat` argument. -/
theorem sum_vonMangoldt_eq_psi (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d = Chebyshev.psi (N : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- **Steps 3 & 4.** `Σ_{d≤N} Λ d / d ≤ log N + (log 4 + 4)`, for `1 ≤ N`. -/
theorem sum_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- lower bound on the divisor-swap sum
  have hlow : (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
        - (∑ d ∈ Finset.Ioc 0 N, Λ d)
      ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hge : (N : ℝ) / d - 1 ≤ ((N / d : ℕ) : ℝ) := cast_div_ge hd.1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd.1
    have : (N : ℝ) * (Λ d / d) - Λ d = Λ d * ((N : ℝ) / d - 1) := by
      have hdne : (d : ℝ) ≠ 0 := hdr.ne'
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hge hΛ
  -- upper bounds: Step 1 and Chebyshev's ψ-bound
  have hstep1 : ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N := by
    rw [← sum_log_eq_sum_vonMangoldt_mul_div]
    exact sum_log_le N
  have hpsi : ∑ d ∈ Finset.Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * N := by
    rw [sum_vonMangoldt_eq_psi]
    exact Chebyshev.psi_le_const_mul_self hNr.le
  -- combine and divide by N
  have hcomb : (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
      ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by
    calc (N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
        = ((N : ℝ) * (∑ d ∈ Finset.Ioc 0 N, Λ d / d)
            - ∑ d ∈ Finset.Ioc 0 N, Λ d) + ∑ d ∈ Finset.Ioc 0 N, Λ d := by ring
      _ ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by
            have := hlow.trans hstep1
            linarith [hpsi]
  -- divide through by N > 0
  rw [← le_div_iff₀' hNr] at hcomb
  have heq : ((N : ℝ) * Real.log N + (Real.log 4 + 4) * N) / N
      = Real.log N + (Real.log 4 + 4) := by
    field_simp
  exact hcomb.trans (le_of_eq heq)

/-! ### Restricting to primes -/

/-- The prime `Nat`s in `range (N+1)` are exactly those in `Ioc 0 N`. -/
theorem filter_prime_range_eq_Ioc (N : ℕ) :
    (Finset.range (N + 1)).filter Nat.Prime = (Finset.Ioc 0 N).filter Nat.Prime := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.pos, by omega⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩

/-- **Mertens' first theorem, upper bound.**
`Σ_{p ≤ N} (log p)/p ≤ log N + (log 4 + 4)`, for `1 ≤ N`. -/
theorem sum_log_div_prime_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p
      ≤ Real.log N + (Real.log 4 + 4) := by
  rw [filter_prime_range_eq_Ioc]
  refine le_trans ?_ (sum_vonMangoldt_div_le hN)
  -- prime subsum of `Λ d / d`, all terms nonneg
  have hsub : (Finset.Ioc 0 N).filter Nat.Prime ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hcongr : ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Real.log p / p
      = ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ p / p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hcongr]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro d _ _
  have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  positivity

/-! ## Step 5 — Abel summation to `Σ 1/p` -/

open MeasureTheory Set intervalIntegral

/-- The Abel-summation weight `f t = 1/log t`. -/
noncomputable def mF (t : ℝ) : ℝ := (Real.log t)⁻¹

/-- The Abel-summation coefficient sequence `c k = (log k)/k · [k prime]`. -/
noncomputable def mC (k : ℕ) : ℝ := if k.Prime then Real.log k / k else 0

theorem mC_zero : mC 0 = 0 := by simp [mC, Nat.not_prime_zero]

theorem mC_one : mC 1 = 0 := by simp [mC, Nat.not_prime_one]

theorem mC_nonneg (k : ℕ) : 0 ≤ mC k := by
  unfold mC
  split
  · rename_i hp
    have : (1 : ℝ) ≤ k := by exact_mod_cast hp.one_lt.le
    have h0 : (0 : ℝ) ≤ Real.log k := Real.log_nonneg this
    positivity
  · exact le_refl 0

/-- `f t = 1/log t` has derivative `-(t·(log t)²)⁻¹` for `t ≥ 2`. -/
theorem hasDerivAt_mF {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt mF (-(x * Real.log x ^ 2)⁻¹) x := by
  have hx0 : x ≠ 0 := by positivity
  have hxlog : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have h2 : HasDerivAt (fun t => (Real.log t)⁻¹) (-x⁻¹ / (Real.log x) ^ 2) x := h1.inv hxlog
  have heq : -x⁻¹ / (Real.log x) ^ 2 = -(x * Real.log x ^ 2)⁻¹ := by
    field_simp
  rw [heq] at h2
  exact h2

theorem differentiableAt_mF {x : ℝ} (hx : 2 ≤ x) : DifferentiableAt ℝ mF x :=
  (hasDerivAt_mF hx).differentiableAt

theorem deriv_mF {x : ℝ} (hx : 2 ≤ x) : deriv mF x = -(x * Real.log x ^ 2)⁻¹ :=
  (hasDerivAt_mF hx).deriv

/-- On `[2, N]`, `deriv mF` agrees with the continuous function
`t ↦ -(t·(log t)²)⁻¹`, hence is integrable there. -/
theorem integrableOn_deriv_mF (N : ℕ) :
    IntegrableOn (deriv mF) (Set.Icc 2 (N : ℝ)) := by
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) := by
    have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 (N : ℝ)) :=
      continuousOn_id.log hne0
    have hbase : ContinuousOn (fun t : ℝ => t * Real.log t ^ 2) (Set.Icc 2 (N : ℝ)) :=
      continuousOn_id.mul (hlogcont.pow 2)
    apply ContinuousOn.neg
    apply hbase.inv₀
    intro t ht
    simp only [Set.mem_Icc] at ht
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have ht0 : (0 : ℝ) < t := by linarith [ht.1]
    positivity
  have hint : IntegrableOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) :=
    hcont.integrableOn_compact isCompact_Icc
  apply hint.congr_fun _ measurableSet_Icc
  intro t ht
  simp only [Set.mem_Icc] at ht
  rw [deriv_mF ht.1]

/-- Prime-sum form of the partial sums `Σ_{k≤M} c k`. -/
theorem sum_mC_Icc_eq (M : ℕ) :
    ∑ k ∈ Finset.Icc 0 M, mC k
      = ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, Real.log p / p := by
  have hset : (Finset.Icc 0 M) = Finset.range (M + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hset]
  unfold mC
  rw [Finset.sum_filter]

theorem sum_mC_Icc_nonneg (M : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 0 M, mC k :=
  Finset.sum_nonneg (fun k _ => mC_nonneg k)

/-- The Step-4 bound, in the `Σ c` shape used by Abel summation. -/
theorem sum_mC_Icc_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 0 M, mC k ≤ Real.log M + (Real.log 4 + 4) := by
  rw [sum_mC_Icc_eq]
  exact sum_log_div_prime_le hM

/-! ### The two elementary integrals -/

/-- `t ↦ 1/(t·log t)` is continuous on `[2, N]`. -/
theorem continuousOn_inv_tlog {N : ℕ} (hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.uIcc 2 (N : ℝ)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Set.uIcc_of_le hle]
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul (continuousOn_id.log hne0))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0 : ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' hlog

/-- `t ↦ 1/(t·(log t)²)` is continuous on `[2, N]`. -/
theorem continuousOn_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.uIcc 2 (N : ℝ)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Set.uIcc_of_le hle]
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul ((continuousOn_id.log hne0).pow 2))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0 : ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog)

/-- `∫₂^N 1/(t·log t) dt = log log N − log log 2`. -/
theorem integral_inv_tlog {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t)⁻¹
      = Real.log (Real.log N) - Real.log (Real.log 2) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcont := continuousOn_inv_tlog hN
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) N,
      HasDerivAt (fun t => Real.log (Real.log t)) ((x * Real.log x)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
    have hinner : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have houter : HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) := Real.hasDerivAt_log hlogne
    have hcomp := houter.comp x hinner
    have hval : (Real.log x)⁻¹ * x⁻¹ = (x * Real.log x)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact hcomp
  have key := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  simpa using key

/-- `∫₂^N 1/(t·(log t)²) dt = 1/log 2 − 1/log N`. -/
theorem integral_inv_tlogsq {N : ℕ} (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..N, (t * Real.log t ^ 2)⁻¹
      = (Real.log 2)⁻¹ - (Real.log N)⁻¹ := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hcont := continuousOn_inv_tlogsq hN
  have hderiv : ∀ x ∈ Set.uIcc (2 : ℝ) N,
      HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have h := (hasDerivAt_mF hx2).neg
    rwa [neg_neg] at h
  have key := integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [key]; ring

/-! ### Main assembly -/

/-- **Mertens' 2nd theorem, upper bound (core estimate).**
For `2 ≤ N`, `Σ_{p ≤ N} 1/p ≤ log log N + C₀` with the explicit constant
`C₀ = 1 + 2·(log 4 + 4)/log 2 − log log 2`. -/
theorem sum_inv_prime_le_aux {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p
      ≤ Real.log (Real.log N)
        + (1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) := by
  have hle : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hle
  set c₀ : ℝ := Real.log 4 + 4 with hc₀
  have hc₀nn : 0 ≤ c₀ := by
    rw [hc₀]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  -- Abel summation
  have habel := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one (N : ℝ)
    (fun t ht => differentiableAt_mF (by simp only [Set.mem_Icc] at ht; exact ht.1))
    (integrableOn_deriv_mF N)
  rw [Nat.floor_natCast] at habel
  -- LHS of Abel = Σ_{p≤N} 1/p
  have hLHS : ∑ k ∈ Finset.Icc 0 N, mF k * mC k
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / p := by
    have hIcc : (Finset.Icc 0 N) = Finset.range (N + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
    rw [hIcc, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    unfold mF mC
    by_cases hk : k.Prime
    · simp only [hk, if_true]
      have hk2 : (1 : ℝ) < k := by exact_mod_cast hk.one_lt
      have hlogk : Real.log k ≠ 0 := ne_of_gt (Real.log_pos hk2)
      field_simp
    · simp only [hk, if_false, mul_zero]
  rw [hLHS] at habel
  rw [habel]
  set B : ℝ := ∑ k ∈ Finset.Icc 0 N, mC k with hB
  have hBle : B ≤ Real.log N + c₀ := sum_mC_Icc_le (by omega)
  have hBnn : 0 ≤ B := sum_mC_Icc_nonneg N
  -- Term 1: `mF N · B ≤ 1 + c₀/log 2`
  have hT1 : mF (N : ℝ) * B ≤ 1 + c₀ / Real.log 2 := by
    have hmul : mF (N : ℝ) * B ≤ (Real.log N)⁻¹ * (Real.log N + c₀) := by
      rw [mF]; exact mul_le_mul_of_nonneg_left hBle (by positivity)
    have hsimp : (Real.log N)⁻¹ * (Real.log N + c₀) = 1 + c₀ / Real.log N := by
      field_simp
    have hfrac : c₀ / Real.log N ≤ c₀ / Real.log 2 :=
      div_le_div_of_nonneg_left hc₀nn hlog2pos hlog2N
    rw [hsimp] at hmul; linarith
  -- The Abel integrand
  set S : ℝ → ℝ := fun t => ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k with hS
  -- Integrability of the two integrands over `Ioc 2 N`
  have hgint : IntegrableOn (fun t => deriv mF t * S t) (Set.Ioc 2 (N : ℝ)) :=
    (integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF N)).mono_set
      Set.Ioc_subset_Icc_self
  have hUcont : ContinuousOn
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) (Set.Icc 2 (N : ℝ)) := by
    have h1 : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc 2 (N : ℝ)) := by
      have := continuousOn_inv_tlogsq hN; rwa [Set.uIcc_of_le hle] at this
    have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) N, t ≠ 0 := by
      intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
    exact h1.mul ((continuousOn_id.log hne0).add continuousOn_const)
  have hUint : IntegrableOn
      (fun t : ℝ => (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) (Set.Ioc 2 (N : ℝ)) :=
    (hUcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  -- Pointwise bound `-U ≤ deriv mF · S` on `Ioc 2 N`
  have hpt : ∀ t ∈ Set.Ioc 2 (N : ℝ),
      -((t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)) ≤ deriv mF t * S t := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have ht2 : (2 : ℝ) ≤ t := le_of_lt ht.1
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hinvnn : (0 : ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by positivity
    -- `S t ≤ log t + c₀`
    have hfloor1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ t))
    have hfloorpos : (0 : ℝ) < (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloor1
    have hSbound : S t ≤ Real.log t + c₀ := by
      rw [hS]
      refine (sum_mC_Icc_le hfloor1).trans ?_
      have : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
        Real.log_le_log hfloorpos (Nat.floor_le ht0.le)
      linarith
    have hderiv : deriv mF t = -(t * Real.log t ^ 2)⁻¹ := deriv_mF ht2
    rw [hderiv]
    have hkey : (t * Real.log t ^ 2)⁻¹ * S t
        ≤ (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀) :=
      mul_le_mul_of_nonneg_left hSbound hinvnn
    nlinarith [hkey]
  -- ⇒  `∫(-U) ≤ ∫ deriv mF · S`
  have hmono : (∫ t in Set.Ioc 2 (N : ℝ), -((t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)))
      ≤ ∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t := by
    refine setIntegral_mono_on ?_ hgint measurableSet_Ioc hpt
    exact hUint.neg
  rw [MeasureTheory.integral_neg] at hmono
  -- Evaluate `∫U`
  have hUeval : ∫ t in Set.Ioc 2 (N : ℝ), (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)
      = (Real.log (Real.log N) - Real.log (Real.log 2))
        + c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) := by
    rw [← intervalIntegral.integral_of_le hle]
    have hsplit : ∫ t in (2 : ℝ)..N, (t * Real.log t ^ 2)⁻¹ * (Real.log t + c₀)
        = ∫ t in (2 : ℝ)..N, ((t * Real.log t)⁻¹ + c₀ * (t * Real.log t ^ 2)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hle, Set.mem_Icc] at ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      have hlog : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
      field_simp
    rw [hsplit, intervalIntegral.integral_add (continuousOn_inv_tlog hN).intervalIntegrable
      ((continuousOn_inv_tlogsq hN).intervalIntegrable.const_mul c₀),
      intervalIntegral.integral_const_mul, integral_inv_tlog hN, integral_inv_tlogsq hN]
  -- Combine everything
  have hIbound : -(∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t)
      ≤ (Real.log (Real.log N) - Real.log (Real.log 2))
        + c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) := by
    rw [← hUeval]; linarith [hmono]
  have hcNpos : 0 ≤ c₀ * (Real.log N)⁻¹ := by positivity
  have hc2 : c₀ * (Real.log 2)⁻¹ = c₀ / Real.log 2 := by rw [div_eq_mul_inv]
  -- final numeric chain
  have hmix : c₀ * ((Real.log 2)⁻¹ - (Real.log N)⁻¹) ≤ c₀ / Real.log 2 := by
    rw [mul_sub, hc2]; linarith [hcNpos]
  -- align the goal's integral (explicit sum) with `S`, and split `2·c₀/log2`
  have hInt_eq : (∫ t in Set.Ioc 2 (N : ℝ),
        deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = ∫ t in Set.Ioc 2 (N : ℝ), deriv mF t * S t := rfl
  rw [hInt_eq, mul_div_assoc]
  linarith [hT1, hIbound, hmix]

/-- **Mertens' 2nd theorem, upper bound.** `Σ_{p ≤ x} 1/p ≤ log log x + C`.
Only the upper direction is needed downstream (N3.4 → N5.2). -/
theorem sum_inv_prime_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p
        ≤ Real.log (Real.log n) + C :=
  ⟨1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2),
    fun _n hn => sum_inv_prime_le_aux hn⟩

/-- Telescoping bound `Σ_{k=2}^{m} (1/(k−1) − 1/k) = 1 − 1/m`. -/
theorem sum_Icc_telescope {m : ℕ} (hm : 2 ≤ m) :
    ∑ k ∈ Finset.Icc 2 m, ((1 : ℝ) / ((k : ℝ) - 1) - 1 / k) = 1 - 1 / m := by
  induction m, hm using Nat.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hm0 : (0 : ℝ) < m := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
    have hm1' : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show ((m : ℝ) + 1 - 1) = (m : ℝ) by ring]
    field_simp
    ring

/-- `Σ_{p ≤ n} 1/(p−1) ≤ log log n + C'`. Since `1/(p−1) = 1/p + 1/(p(p−1))`
and `Σ_{k≥2} 1/(k(k−1))` telescopes to `≤ 1`, this follows from
`sum_inv_prime_le` with `C' = C + 1` (the brute `1/(p−1) ≤ 2/p` termwise
bound only gives `2·log log n`, so is not used). -/
theorem sum_inv_prime_sub_one_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
        ≤ Real.log (Real.log n) + C := by
  obtain ⟨C, hC⟩ := sum_inv_prime_le
  refine ⟨C + 1, fun n hn => ?_⟩
  have hmain := hC n hn
  -- split `1/(p−1) = 1/p + (1/(p−1) − 1/p)`
  have hsplit : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
      = (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
        + ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hsplit]
  -- tail `≤ 1` via telescoping
  have htail : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) ≤ 1 := by
    have hsub : (Finset.range (n + 1)).filter Nat.Prime ⊆ Finset.Icc 2 n := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, by omega⟩
    have hnn : ∀ k ∈ Finset.Icc 2 n, 0 ≤ (1 : ℝ) / ((k : ℝ) - 1) - 1 / k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
      have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hkk : (k : ℝ) - 1 ≤ k := by linarith
      have := one_div_le_one_div_of_le hk1 hkk
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hnn k hk)).trans ?_
    rw [sum_Icc_telescope hn]
    have hnpos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  linarith [hmain, htail]

end Salt.Maynard

-- ==== upstream: Salt/BrunLower/MertensWindow.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# The windowed Mertens second theorem, upper form (blueprint `p0`, node PM1)

`∑_{w ≤ p < z} 1/p ≤ log(log z / log w) + C₃ / log w` for `2 ≤ w ≤ z`, with `C₃ = 19`
an explicit numeral.  The Mertens constant `M` **cancels** in the window (never defined).

Route (classical Mertens 1874, all elementary):

1. **Mertens-1 LOWER** `∑_{p ≤ N} (log p)/p ≥ log N − C_low` (the genuinely new piece; the
   corpus `Salt/Maynard/Mertens.lean` has only the UPPER `sum_log_div_prime_le`).  Via the
   log-factorial identity `∑_{n ≤ N} log n = log N!`, the Stirling floor
   `log N! ≥ N log N − N` (mathlib `Real.le_log_factorial_stirling`), `⌊N/d⌋ ≤ N/d`, and the
   prime-power strip `∑_{d ≤ N} Λ(d)/d − ∑_{p ≤ N} (log p)/p ≤ 5/2` (geometric comparison +
   `∑ (log n)/n² ≤ 5/4` by an integral bound).
2. **Two-sided `R`** `|∑_{p ≤ t} (log p)/p − log t| ≤ 6` for real `t ≥ 2` (corpus upper + the
   new lower + floor slop).
3. **The Abel windowed pass** (corpus `mF = 1/log t` machinery, difference of two Abel passes):
   the main term telescopes to `∫_w^z dt/(t log t) = log(log z/log w)` exactly; the `R`-terms
   give `≤ 3·6/log w`.

Reuses the corpus Abel machinery (`Salt.Maynard.mF`, `mC`, `hasDerivAt_mF`, `deriv_mF`,
`integral_inv_tlog`, `sum_mC_Icc_eq`, `sum_log_div_prime_le`, …) rather than rebuilding it.
-/

open Finset ArithmeticFunction MeasureTheory Set intervalIntegral

namespace Salt.BrunLower

open Salt.Maynard

/-! ## Section 1 — Mertens' first theorem, LOWER bound -/

/-- `∑_{n ∈ Ioc 0 N} log n = log N!` (the log-factorial identity). -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = Real.log (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- **Mertens' first theorem, LOWER bound (von Mangoldt form).**
`∑_{d ≤ N} Λ(d)/d ≥ log N − 1`, for `1 ≤ N`.  From `∑ Λ(d)·⌊N/d⌋ = log N! ≥ N log N − N`. -/
theorem sum_vonMangoldt_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- Stirling floor: `N log N − N ≤ log N!`
  have hstir : (N : ℝ) * Real.log N - N ≤ Real.log (Nat.factorial N : ℝ) := by
    have h := Stirling.le_log_factorial_stirling (n := N) (by omega)
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      have := Real.pi_gt_three; linarith
    linarith
  -- `∑ log n = log N!`, and `∑ Λ(d)⌊N/d⌋ = ∑ log n`
  rw [← sum_log_eq_log_factorial, sum_log_eq_sum_vonMangoldt_mul_div] at hstir
  -- `∑ Λ(d)⌊N/d⌋ ≤ N · ∑ Λ(d)/d`
  have hup : ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hfloor hΛ
      _ = (N : ℝ) * (Λ d / d) := by ring
  -- combine and divide by N
  have hcomb : (N : ℝ) * Real.log N - N ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d :=
    le_trans hstir hup
  have hfac : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
    nlinarith [hcomb]
  exact le_of_mul_le_mul_left hfac hNr

/-! ## Section 2 — the prime-power strip -/

/-- summand `(log t)/t²`. -/
private noncomputable def lsF (t : ℝ) : ℝ := Real.log t / t ^ 2

/-- antiderivative `-(1+log t)/t`, with `(lsG)' = lsF`. -/
private noncomputable def lsG (t : ℝ) : ℝ := -(1 + Real.log t) / t

private theorem hasDerivAt_lsG {x : ℝ} (hx : 0 < x) : HasDerivAt lsG (lsF x) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h1 : HasDerivAt (fun t => -(1 + Real.log t)) (-x⁻¹) x :=
    ((Real.hasDerivAt_log hx0).const_add (1 : ℝ)).neg
  have h2 : HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
  have hprod := h1.mul h2
  have heq : -x⁻¹ * x⁻¹ + -(1 + Real.log x) * -(x ^ 2)⁻¹ = lsF x := by
    rw [lsF]; field_simp; ring
  have hmain : HasDerivAt (fun t => -(1 + Real.log t) * t⁻¹) (lsF x) x := by
    rw [← heq]; exact hprod
  have hg : lsG = fun t => -(1 + Real.log t) * t⁻¹ := by
    funext t; rw [lsG]; ring
  rw [hg]; exact hmain

private theorem hasDerivAt_lsF {x : ℝ} (hx : 0 < x) :
    HasDerivAt lsF ((x⁻¹ * x ^ 2 - Real.log x * (2 * x)) / (x ^ 2) ^ 2) x := by
  have hc : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hd : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hd0 : x ^ 2 ≠ 0 := by positivity
  exact hc.div hd hd0

private theorem antitoneOn_lsF {b : ℝ} : AntitoneOn lsF (Set.Icc 2 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 2 b)
  · apply ContinuousOn.div (continuousOn_id.log ?_) (continuousOn_id.pow 2) ?_
    · intro t ht; simp only [Set.mem_Icc] at ht
      exact (by linarith [ht.1] : (0:ℝ) < t).ne'
    · intro t ht; simp only [Set.mem_Icc] at ht
      have ht0 : (0:ℝ) < t := by linarith [ht.1]
      exact pow_ne_zero 2 ht0.ne'
  · rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    exact (hasDerivAt_lsF hx0).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    rw [(hasDerivAt_lsF hx0).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx.1.le
      have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hxx : x⁻¹ * x ^ 2 = x := by field_simp
      rw [hxx]
      nlinarith [mul_pos hx0 (by linarith [hlog, hl2] : (0:ℝ) < 2 * Real.log x - 1)]
    · positivity

private theorem continuousOn_lsF {b : ℝ} (hb : 2 ≤ b) :
    ContinuousOn lsF (Set.uIcc 2 b) := by
  rw [Set.uIcc_of_le hb]
  apply ContinuousOn.div (continuousOn_id.log ?_) (continuousOn_id.pow 2) ?_
  · intro t ht; simp only [Set.mem_Icc] at ht
    exact (by linarith [ht.1] : (0:ℝ) < t).ne'
  · intro t ht; simp only [Set.mem_Icc] at ht
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    exact pow_ne_zero 2 ht0.ne'

private theorem integral_lsF {b : ℝ} (hb : 2 ≤ b) :
    ∫ x in (2:ℝ)..b, lsF x = lsG b - lsG 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) b, HasDerivAt lsG (lsF x) x := by
    intro x hx
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hx
    exact hasDerivAt_lsG (by linarith [hx.1])
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_lsF hb).intervalIntegrable

/-- `∑_{n ∈ Ioc 1 N} (log n)/n² ≤ 5/4`. -/
theorem sum_lsF_le (N : ℕ) : ∑ n ∈ Finset.Ioc 1 N, lsF n ≤ 5/4 := by
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlsF2 : lsF ((2:ℕ):ℝ) ≤ 1/4 := by
    rw [lsF]; push_cast
    rw [div_le_iff₀ (by norm_num)]; nlinarith [hlog2]
  rcases le_or_gt N 2 with hN | hN
  · interval_cases N
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; norm_num
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; norm_num
    · rw [show Finset.Ioc 1 2 = {2} by rfl, Finset.sum_singleton]; linarith
  · have hsplit : ∑ n ∈ Finset.Ioc 1 N, lsF n
        = lsF ((2:ℕ):ℝ) + ∑ n ∈ Finset.Ioc 2 N, lsF n := by
      rw [← Finset.sum_Ioc_consecutive (fun i => lsF (i:ℝ))
        (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) ≤ N)]
      rw [show Finset.Ioc 1 2 = {2} by rfl, Finset.sum_singleton]
    have hmap : Finset.Ioc 2 N
        = (Finset.Ico 2 N).map ⟨fun i => i + 1, fun a b h => by simpa using h⟩ := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨n - 1, ⟨by omega, by omega⟩, ?_⟩
        show n - 1 + 1 = n
        omega
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        show 2 < i + 1 ∧ i + 1 ≤ N
        omega
    have hreindex : ∑ n ∈ Finset.Ioc 2 N, lsF (n:ℝ)
        = ∑ i ∈ Finset.Ico 2 N, lsF ((i + 1 : ℕ) : ℝ) := by
      rw [hmap, Finset.sum_map]; rfl
    have hcomp : ∑ i ∈ Finset.Ico 2 N, lsF ((i + 1 : ℕ) : ℝ) ≤ ∫ x in (2:ℝ)..(N:ℝ), lsF x :=
      AntitoneOn.sum_le_integral_Ico (by omega : (2:ℕ) ≤ N) antitoneOn_lsF
    have hint : (∫ x in (2:ℝ)..(N:ℝ), lsF x) ≤ (1 + Real.log 2)/2 := by
      rw [integral_lsF (by exact_mod_cast (by omega : (2:ℕ) ≤ N))]
      have hN2 : (2:ℝ) ≤ N := by exact_mod_cast (by omega : (2:ℕ) ≤ N)
      have hlsGN : lsG (N:ℝ) ≤ 0 := by
        rw [lsG]
        apply div_nonpos_of_nonpos_of_nonneg
        · have := Real.log_nonneg (by linarith : (1:ℝ) ≤ N); linarith
        · linarith
      have hg2 : lsG 2 = -(1 + Real.log 2)/2 := by rw [lsG]
      rw [hg2]; linarith
    rw [hsplit, hreindex]
    linarith [hcomp.trans hint, hlsF2]

/-- **The prime-power strip.** `∑_{d ≤ N} Λ(d)/d ≤ ∑_{p ≤ N} (log p)/p + 5/2`. -/
theorem sum_vonMangoldt_div_le_prime (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d
      ≤ (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p) + 5/2 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ d ∈ Finset.Ioc 0 N, Λ d / d
      = (∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / d)
        + ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / d :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : ∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / d
      = ∑ p ∈ P, Real.log p / p := by
    rw [hP, ← filter_prime_range_eq_Ioc]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hsplit, hprime]
  suffices hstrip : ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / d ≤ 5/2 by
    linarith [hstrip]
  set S' := (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d) with hS'
  set T := P ×ˢ Finset.Icc 2 N with hT
  set φ : ℕ × ℕ → ℕ := fun pk => pk.1 ^ pk.2 with hφ
  have hzero : ∑ d ∈ S', Λ d / d = ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro d hd hd'
    simp only [Finset.mem_filter, not_and, not_not] at hd'
    rw [hd' hd, zero_div]
  have hsub : S'.filter (fun d => Λ d ≠ 0) ⊆ T.image φ := by
    intro d hd
    rw [Finset.mem_filter, hS', Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨⟨hd0, hdN⟩, hdnp⟩, hdΛ⟩ := hd
    have hpp : IsPrimePow d := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hdΛ
    have hd1 : d ≠ 1 := by
      rintro rfl; exact hdΛ (by simp [ArithmeticFunction.vonMangoldt_apply_one])
    have hpprime : (d.minFac).Prime := Nat.minFac_prime hd1
    have hpk : d.minFac ^ (d.factorization d.minFac) = d := hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ d.factorization d.minFac := by
      rcases Nat.lt_or_ge (d.factorization d.minFac) 2 with h | h
      · interval_cases hkk : d.factorization d.minFac
        · rw [pow_zero] at hpk; exact absurd hpk.symm hd1
        · rw [pow_one] at hpk; rw [hpk] at hpprime; exact absurd hpprime hdnp
      · exact h
    have hkN : d.factorization d.minFac ≤ N := by
      have h1 : d.factorization d.minFac < 2 ^ (d.factorization d.minFac) :=
        (d.factorization d.minFac).lt_two_pow_self
      have h2 : 2 ^ (d.factorization d.minFac) ≤ d.minFac ^ (d.factorization d.minFac) :=
        Nat.pow_le_pow_left hpprime.two_le _
      omega
    rw [Finset.mem_image]
    refine ⟨(d.minFac, d.factorization d.minFac), ?_, hpk⟩
    rw [hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have hpN : d.minFac ≤ N := le_trans (Nat.minFac_le hd0) hdN
    exact ⟨⟨by omega, hpprime⟩, hk2, hkN⟩
  have hle1 : ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d ≤ ∑ d ∈ T.image φ, Λ d / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
  have hsumimg : ∑ d ∈ T.image φ, Λ d / d = ∑ pk ∈ T, Λ (φ pk) / (φ pk) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hxp⟩, hxk2, _⟩ := hx
    obtain ⟨⟨_, hyp⟩, hyk2, _⟩ := hy
    simp only [hφ] at hxy
    have hp1 : (x.1 ^ x.2).minFac = x.1 := hxp.pow_minFac (by omega)
    have hp2 : (y.1 ^ y.2).minFac = y.1 := hyp.pow_minFac (by omega)
    have heqbase : x.1 = y.1 := by rw [← hp1, ← hp2, hxy]
    have heqexp : x.2 = y.2 :=
      Nat.pow_right_injective hxp.two_le (by rw [hxy, ← heqbase] : x.1 ^ x.2 = x.1 ^ y.2)
    exact Prod.ext heqbase heqexp
  have hval : ∑ pk ∈ T, Λ (φ pk) / (φ pk) = ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2 := by
    apply Finset.sum_congr rfl
    intro pk hpk
    rw [hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hpk
    obtain ⟨⟨_, hprime⟩, hk2, _⟩ := hpk
    simp only [hφ]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : pk.2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hprime, Nat.cast_pow]
  have hprod : ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2
      = ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k := by
    rw [hT, Finset.sum_product]
  have hgeom : ∀ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k
      ≤ 2 * (Real.log p / (p:ℝ) ^ 2) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hfac : ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k
        = Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [inv_pow]; ring
    rw [hfac]
    have hq0 : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
    have hqhalf : (p:ℝ)⁻¹ ≤ 1/2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hb : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by linarith
    have hq : ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k ≤ 2 * ((p:ℝ)⁻¹) ^ 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have h1 := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) (x := (p:ℝ)⁻¹) hq0 (by linarith)
      have hq1 : ((p:ℝ)⁻¹) ^ 2 / (1 - (p:ℝ)⁻¹) ≤ 2 * ((p:ℝ)⁻¹) ^ 2 := by
        rw [div_le_iff₀ hb]
        nlinarith [mul_nonneg (sq_nonneg ((p:ℝ)⁻¹)) (by linarith : (0:ℝ) ≤ 1 - 2 * (p:ℝ)⁻¹)]
      linarith [h1, hq1]
    calc Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k
        ≤ Real.log p * (2 * ((p:ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hq hlogp
      _ = 2 * (Real.log p / (p:ℝ) ^ 2) := by rw [inv_pow]; ring
  have hPsub : P ⊆ Finset.Ioc 1 N := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Ioc]
    exact ⟨hp.2.one_lt, by omega⟩
  have hlsFsum : (2:ℝ) * ∑ p ∈ P, lsF p ≤ 2 * ∑ n ∈ Finset.Ioc 1 N, lsF n := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg hPsub
    intro n hn _
    rw [Finset.mem_Ioc] at hn
    rw [lsF]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (by positivity)
  calc ∑ d ∈ S', Λ d / d
      = ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d := hzero
    _ ≤ ∑ d ∈ T.image φ, Λ d / d := hle1
    _ = ∑ pk ∈ T, Λ (φ pk) / (φ pk) := hsumimg
    _ = ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2 := hval
    _ = ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k := hprod
    _ ≤ ∑ p ∈ P, 2 * (Real.log p / (p:ℝ) ^ 2) := Finset.sum_le_sum hgeom
    _ = 2 * ∑ p ∈ P, lsF p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; rw [lsF]
    _ ≤ 2 * ∑ n ∈ Finset.Ioc 1 N, lsF n := hlsFsum
    _ ≤ 2 * (5/4) := by linarith [sum_lsF_le N]
    _ = 5/2 := by norm_num

/-! ## Section 3 — the two-sided estimate `|∑_{p ≤ t} (log p)/p − log t| ≤ 6` -/

/-- The partial-sum function `S(t) = ∑_{p ≤ ⌊t⌋} (log p)/p`, in the corpus' `mC` form. -/
noncomputable def Sfun (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k

/-- **The two-sided Mertens-1 estimate.** `|S(t) − log t| ≤ 6` for real `t ≥ 2`; combines the
corpus UPPER bound with the new LOWER bound and the prime-power strip, absorbing the `⌊t⌋`-vs-`t`
slop. -/
theorem abs_Sfun_sub_log_le {t : ℝ} (ht : 2 ≤ t) : |Sfun t - Real.log t| ≤ 6 := by
  have hM2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by push_cast; linarith : ((2:ℕ):ℝ) ≤ t)
  have hMt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htM1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hM2R : (2:ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hM2
  have hMpos : (0:ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have hSeq : Sfun t = ∑ p ∈ (Finset.range (⌊t⌋₊ + 1)).filter Nat.Prime, Real.log p / p := by
    rw [Sfun, sum_mC_Icc_eq]
  -- `log t ≤ log ⌊t⌋ + 1/2`
  have hlogtM : Real.log t ≤ Real.log ⌊t⌋₊ + 1/2 := by
    have h1 : Real.log t ≤ Real.log ((⌊t⌋₊ : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log ((⌊t⌋₊ : ℝ) + 1) - Real.log ⌊t⌋₊ ≤ 1/2 := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have heq : ((⌊t⌋₊ : ℝ) + 1) / ⌊t⌋₊ = 1 + 1 / ⌊t⌋₊ := by field_simp
      rw [heq]
      have hle := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + 1 / (⌊t⌋₊ : ℝ))
      have hMhalf : 1 / (⌊t⌋₊ : ℝ) ≤ 1/2 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM2)
      linarith
    linarith
  -- UPPER
  have hUp : Sfun t ≤ Real.log t + (Real.log 4 + 4) := by
    rw [hSeq]
    have h := sum_log_div_prime_le (N := ⌊t⌋₊) (by omega)
    have hlogMt : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hMpos hMt
    linarith
  -- LOWER
  have hLow : Real.log t - 4 ≤ Sfun t := by
    rw [hSeq]
    have hge := sum_vonMangoldt_div_ge (N := ⌊t⌋₊) (by omega)
    have hstrip := sum_vonMangoldt_div_le_prime ⌊t⌋₊
    linarith [hge, hstrip, hlogtM]
  -- combine, using `log 4 ≤ 2`
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; nlinarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## Section 4 — real-endpoint integrals and integrability (corpus templates) -/

/-- `deriv mF` is integrable on `[2, b]` (real endpoint). -/
theorem integrableOn_deriv_mF_real {b : ℝ} (_hb : 2 ≤ b) :
    IntegrableOn (deriv mF) (Set.Icc 2 b) := by
  have hne0 : ∀ t ∈ Set.Icc (2:ℝ) b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 b) := by
    have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 b) :=
      continuousOn_id.log hne0
    have hbase : ContinuousOn (fun t : ℝ => t * Real.log t ^ 2) (Set.Icc 2 b) :=
      continuousOn_id.mul (hlogcont.pow 2)
    apply ContinuousOn.neg
    apply hbase.inv₀
    intro t ht
    simp only [Set.mem_Icc] at ht
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hint : IntegrableOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 b) :=
    hcont.integrableOn_compact isCompact_Icc
  apply hint.congr_fun _ measurableSet_Icc
  intro t ht
  simp only [Set.mem_Icc] at ht
  rw [deriv_mF ht.1]

theorem continuousOn_inv_tlog_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hne0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul (continuousOn_id.log hne0))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' hlog

theorem continuousOn_inv_tlogsq_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hne0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul ((continuousOn_id.log hne0).pow 2))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog)

/-- `∫_a^b 1/(t·log t) dt = log log b − log log a` for `2 ≤ a ≤ b`. -/
theorem integral_inv_tlog_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t * Real.log t)⁻¹ = Real.log (Real.log b) - Real.log (Real.log a) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => Real.log (Real.log t)) ((x * Real.log x)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have hinner : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have houter : HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) :=
      Real.hasDerivAt_log (ne_of_gt hlogpos)
    have hcomp := houter.comp x hinner
    have hval : (Real.log x)⁻¹ * x⁻¹ = (x * Real.log x)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact hcomp
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_inv_tlog_real ha hab).intervalIntegrable
  simpa using key

/-- `∫_a^b 1/(t·(log t)²) dt = 1/log a − 1/log b` for `2 ≤ a ≤ b`. -/
theorem integral_inv_tlogsq_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t * Real.log t ^ 2)⁻¹ = (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    have hx2 : (2:ℝ) ≤ x := by linarith [hx.1]
    have h := (hasDerivAt_mF hx2).neg
    rwa [neg_neg] at h
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_inv_tlogsq_real ha hab).intervalIntegrable
  rw [key]; ring

/-! ## Section 5 — the Abel windowed pass (difference of two Abel passes) -/

/-- **The windowed Abel core.** `∑_{p ≤ ⌊z⌋} (log p)/p·(1/log p) − (same at w) ≤ log(log z/log w)
+ 18/log w`, in the `mF·mC` (Abel) form.  The Mertens constant cancels; only the two-sided `R`-term
(`|S(t) − log t| ≤ 6`) survives, weighted to `O(1/log w)`. -/
theorem window_core {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mF k * mC k) - (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mF k * mC k)
      ≤ Real.log (Real.log z / Real.log w) + 18 / Real.log w := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlwne : Real.log w ≠ 0 := ne_of_gt hlogw
  have hlzne : Real.log z ≠ 0 := ne_of_gt hlogz
  have hlogwz : Real.log w ≤ Real.log z := Real.log_le_log (by linarith) hwz
  have hinvzw : (Real.log z)⁻¹ ≤ (Real.log w)⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hlogw hlogwz
  have hinvz0 : (0:ℝ) ≤ (Real.log z)⁻¹ := by positivity
  have hinvw0 : (0:ℝ) ≤ (Real.log w)⁻¹ := by positivity
  have hGint_z : IntegrableOn (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      (Set.Icc 2 z) :=
    integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF_real hz)
  have hII_2w : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume 2 w := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hw]
    exact hGint_z.mono_set (Set.Icc_subset_Icc le_rfl hwz)
  have hII_wz : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume w z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hwz]
    exact hGint_z.mono_set (Set.Icc_subset_Icc hw le_rfl)
  have habelz := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one z
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hz)
  have habelw := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one w
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hw)
  rw [← intervalIntegral.integral_of_le hz,
    show (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mC k) = Sfun z from rfl] at habelz
  rw [← intervalIntegral.integral_of_le hw,
    show (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mC k) = Sfun w from rfl] at habelw
  have hadd : (∫ t in (2:ℝ)..w, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      + (∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = ∫ t in (2:ℝ)..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k :=
    intervalIntegral.integral_add_adjacent_intervals hII_2w hII_wz
  have hpt : ∀ t ∈ Set.Icc w z,
      -(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹
        ≤ deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have ht2 : (2:ℝ) ≤ t := le_trans hw ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hinvnn : (0:ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by positivity
    have hSt : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k) ≤ Real.log t + 6 := by
      have := abs_Sfun_sub_log_le ht2
      rw [abs_le] at this
      have hSeq : Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := rfl
      linarith [this.2]
    rw [deriv_mF ht2]
    have hkey : (t * Real.log t ^ 2)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
        ≤ (t * Real.log t ^ 2)⁻¹ * (Real.log t + 6) :=
      mul_le_mul_of_nonneg_left hSt hinvnn
    have hsplit : (t * Real.log t ^ 2)⁻¹ * (Real.log t + 6)
        = (t * Real.log t)⁻¹ + 6 * (t * Real.log t ^ 2)⁻¹ := by
      have hne : Real.log t ≠ 0 := ne_of_gt hlogt
      field_simp
    nlinarith [hkey, hsplit]
  have hIntA : (∫ t in w..z, -(t * Real.log t)⁻¹)
      = -(Real.log (Real.log z) - Real.log (Real.log w)) := by
    rw [intervalIntegral.integral_neg, integral_inv_tlog_real hw hwz]
  have hIntB : (∫ t in w..z, 6 * (t * Real.log t ^ 2)⁻¹)
      = 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_tlogsq_real hw hwz]
  have hAintble : IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) volume w z :=
    ((continuousOn_inv_tlog_real hw hwz).intervalIntegrable).neg
  have hBintble : IntervalIntegrable (fun t => 6 * (t * Real.log t ^ 2)⁻¹) volume w z :=
    ((continuousOn_inv_tlogsq_real hw hwz).intervalIntegrable).const_mul 6
  have hLint : (∫ t in w..z, (-(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹))
      = -(Real.log (Real.log z) - Real.log (Real.log w))
        - 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_sub hAintble hBintble, hIntA, hIntB]
  have hmono : (∫ t in w..z, (-(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹))
      ≤ ∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k :=
    intervalIntegral.integral_mono_on hwz (hAintble.sub hBintble) hII_wz hpt
  have hSz := abs_Sfun_sub_log_le hz
  have hSw := abs_Sfun_sub_log_le hw
  rw [abs_le] at hSz hSw
  have hAbound : mF z * Sfun z ≤ 1 + 6 * (Real.log w)⁻¹ := by
    have hmFz : mF z = (Real.log z)⁻¹ := rfl
    calc mF z * Sfun z = (Real.log z)⁻¹ * Sfun z := by rw [hmFz]
      _ ≤ (Real.log z)⁻¹ * (Real.log z + 6) := by
          apply mul_le_mul_of_nonneg_left _ hinvz0; linarith [hSz.2]
      _ = 1 + 6 * (Real.log z)⁻¹ := by rw [mul_add, inv_mul_cancel₀ hlzne]; ring
      _ ≤ 1 + 6 * (Real.log w)⁻¹ := by linarith [hinvzw]
  have hBbound : 1 - 6 * (Real.log w)⁻¹ ≤ mF w * Sfun w := by
    have hmFw : mF w = (Real.log w)⁻¹ := rfl
    calc 1 - 6 * (Real.log w)⁻¹ = (Real.log w)⁻¹ * (Real.log w - 6) := by
          rw [mul_sub, inv_mul_cancel₀ hlwne]; ring
      _ ≤ (Real.log w)⁻¹ * Sfun w := by
          apply mul_le_mul_of_nonneg_left _ hinvw0; linarith [hSw.1]
      _ = mF w * Sfun w := by rw [hmFw]
  rw [Real.log_div hlzne hlwne, div_eq_mul_inv]
  linarith [habelz, habelw, hadd, hmono, hLint, hAbound, hBbound]

/-! ## Section 6 — packaging into `primesInWindow` and the PM2-consumable forms -/

/-- The Abel LHS is the prime reciprocal sum `∑_{p ≤ ⌊b⌋} 1/p`. -/
theorem sum_mF_mul_mC_eq (b : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, mF k * mC k
      = ∑ p ∈ (Finset.range (⌊b⌋₊ + 1)).filter Nat.Prime, (1:ℝ) / p := by
  have hIcc : Finset.Icc 0 ⌊b⌋₊ = Finset.range (⌊b⌋₊ + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hIcc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  unfold mF mC
  by_cases hk : k.Prime
  · simp only [hk, if_true]
    have hk2 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
    have hlogk : Real.log k ≠ 0 := ne_of_gt (Real.log_pos hk2)
    field_simp
  · simp only [hk, if_false, mul_zero]

/-- Primes in the window `[w, z)`, packaged over `range ⌈z⌉₊`.  Since `p ∈ range ⌈z⌉₊ ↔ (p:ℝ) < z`,
this is exactly the set of primes `p` with `w ≤ p < z`. -/
noncomputable def primesInWindow (w z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter (fun p => Nat.Prime p ∧ w ≤ (p : ℝ))

/-- **The windowed Mertens bound, general carrier (PM2's consumable form).** Any finite set of
primes `p` with `w ≤ p < z` obeys `∑ 1/p ≤ log(log z/log w) + 19/log w` for `2 ≤ w ≤ z`. -/
theorem sum_inv_le_of_prime_window {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hfloorwz : ⌊w⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hwz
  set Wz := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime with hWz
  set Ww := (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime with hWw
  have hWwWz : Ww ⊆ Wz := by
    rw [hWw, hWz]; apply Finset.filter_subset_filter
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have hSsub : S ⊆ insert ⌊w⌋₊ (Wz \ Ww) := by
    intro p hp
    obtain ⟨hpp, hwp, hpz⟩ := hS p hp
    rw [Finset.mem_insert]
    by_cases hpw : (p : ℝ) ≤ w
    · left
      have heq : (p : ℝ) = w := le_antisymm hpw hwp
      rw [← heq, Nat.floor_natCast]
    · right
      rw [not_le] at hpw
      have hfloorw_lt : ⌊w⌋₊ < p := by
        have h1 : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le (by linarith)
        have : (⌊w⌋₊ : ℝ) < p := by linarith
        exact_mod_cast this
      have hpfloorz : p ≤ ⌊z⌋₊ := Nat.le_floor hpz.le
      rw [Finset.mem_sdiff, hWz, hWw, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
        Finset.mem_range, not_and]
      exact ⟨⟨by omega, hpp⟩, fun hlt _ => by omega⟩
  have hnn : ∀ p ∈ insert ⌊w⌋₊ (Wz \ Ww), p ∉ S → 0 ≤ (1 : ℝ) / p := fun p _ _ => by positivity
  have hstep1 : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub hnn
  have hins : ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p
      ≤ 1 / (⌊w⌋₊ : ℝ) + ∑ p ∈ Wz \ Ww, (1 : ℝ) / p := by
    by_cases hmem : ⌊w⌋₊ ∈ Wz \ Ww
    · rw [Finset.insert_eq_self.mpr hmem]
      have : (0:ℝ) ≤ 1 / (⌊w⌋₊ : ℝ) := by positivity
      linarith
    · rw [Finset.sum_insert hmem]
  have hsdiff : ∑ p ∈ Wz \ Ww, (1 : ℝ) / p
      = (∑ p ∈ Wz, (1 : ℝ) / p) - ∑ p ∈ Ww, (1 : ℝ) / p := by
    rw [eq_sub_iff_add_eq]; exact Finset.sum_sdiff hWwWz
  have hcore := window_core hw hwz
  rw [sum_mF_mul_mC_eq z, sum_mF_mul_mC_eq w, ← hWz, ← hWw] at hcore
  have hfloorlog : Real.log w ≤ (⌊w⌋₊ : ℝ) := by
    have h1 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : w < (⌊w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w
    linarith
  have hfloorinv : 1 / (⌊w⌋₊ : ℝ) ≤ 1 / Real.log w := one_div_le_one_div_of_le hlogw hfloorlog
  have hsplit : (1:ℝ) / Real.log w + 18 / Real.log w = 19 / Real.log w := by
    rw [← add_div]; norm_num
  calc ∑ p ∈ S, (1 : ℝ) / p
      ≤ ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p := hstep1
    _ ≤ 1 / (⌊w⌋₊ : ℝ) + ∑ p ∈ Wz \ Ww, (1 : ℝ) / p := hins
    _ = 1 / (⌊w⌋₊ : ℝ) + ((∑ p ∈ Wz, (1 : ℝ) / p) - ∑ p ∈ Ww, (1 : ℝ) / p) := by rw [hsdiff]
    _ ≤ 1 / Real.log w + (Real.log (Real.log z / Real.log w) + 18 / Real.log w) := by
        linarith [hcore, hfloorinv]
    _ = Real.log (Real.log z / Real.log w) + 19 / Real.log w := by linarith [hsplit]

/-- **The frozen PM1 target.** `∑_{w ≤ p < z} 1/p ≤ log(log z/log w) + 19/log w` for `2 ≤ w ≤ z`.
`w₀ = 2`, `C₃ = 19`. -/
theorem sum_inv_prime_window_le {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    ∑ p ∈ primesInWindow w z, (1 : ℝ) / p
      ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  apply sum_inv_le_of_prime_window hw hwz
  intro p hp
  rw [primesInWindow, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨hp.2.1, hp.2.2, Nat.lt_ceil.mp hp.1⟩

/-- **Subset monotonicity** (what PM2 consumes for `windowPrimes s Lam z n ⊆ …`). -/
theorem sum_inv_le_of_subset_window {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : S ⊆ primesInWindow w z) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  apply sum_inv_le_of_prime_window hw hwz
  intro p hp
  have hmem := hS hp
  rw [primesInWindow, Finset.mem_filter, Finset.mem_range] at hmem
  exact ⟨hmem.2.1, hmem.2.2, Nat.lt_ceil.mp hmem.1⟩

end Salt.BrunLower

-- ==== upstream: Salt/Mertens/Second.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/



/-!
# The sharp Mertens second theorem

`∃ M C, 0 ≤ C ∧ ∀ n ≥ 2, |Σ_{p≤n} 1/p − (log log n + M)| ≤ C / log n`.

Route (classical Abel summation against the two-sided Mertens-1 window):
The corpus provides the Abel identity `Σ_{p≤x} 1/p = mF x · Sfun x − ∫₂ˣ mF'·Sfun`
(`sum_mul_eq_sub_integral_mul₁`) and the load-bearing two-sided estimate
`|Sfun t − log t| ≤ 6` (`abs_Sfun_sub_log_le`).  Writing `Sfun = log + E`
(`|E| ≤ 6`), the `log`-part yields `1 + log log x − log log 2`, and the
`E`-part is the improper integral `∫₂^∞ E(t)/(t log²t) dt`, which converges
absolutely (`|E| ≤ 6`, `∫ (t log²t)⁻¹ < ∞`).  The Meissel–Mertens constant is
`M := 1 − log log 2 + ∫₂^∞ E/(t log²t)`; the error is
`E(x)/log x − ∫ₓ^∞ E/(t log²t)`, each piece `≤ 6/log x`, so `C = 12`.
-/

open Finset MeasureTheory Set Filter Topology intervalIntegral

namespace Salt.Mertens

open Salt.Maynard Salt.BrunLower

/-- The `E`-part integrand `E(t)/(t log²t)` where `E(t) = Sfun t − log t`. -/
noncomputable def hInt (t : ℝ) : ℝ := (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹

/-! ## Tail integrals of the dominating function `(t log²t)⁻¹` on `Ioi a` -/

/-- `t ↦ -(log t)⁻¹` is an antiderivative of `(t log²t)⁻¹` for `t ≥ 2`. -/
theorem hasDerivAt_negInvLog {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
  have h := (hasDerivAt_mF hx).neg
  rw [neg_neg] at h
  exact h

/-- `-(log t)⁻¹ → 0` at `atTop`. -/
theorem tendsto_negInvLog : Tendsto (fun t : ℝ => -(Real.log t)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (Real.log t)⁻¹) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  simpa using h1.neg

/-- The dominating function `(t log²t)⁻¹` is integrable on `(a, ∞)` for `a ≥ 2`. -/
theorem integrableOn_invtlogsq_Ioi {a : ℝ} (ha : 2 ≤ a) :
    IntegrableOn (fun t => (t * Real.log t ^ 2)⁻¹) (Set.Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_negInvLog (le_trans ha (Set.mem_Ici.mp hx))) (fun x hx => ?_)
    tendsto_negInvLog
  have hx2 : (0:ℝ) < x := by have := Set.mem_Ioi.mp hx; linarith
  positivity

/-- `∫ₐ^∞ (t log²t)⁻¹ = 1/log a` for `a ≥ 2`. -/
theorem integral_invtlogsq_Ioi {a : ℝ} (ha : 2 ≤ a) :
    ∫ t in Set.Ioi a, (t * Real.log t ^ 2)⁻¹ = (Real.log a)⁻¹ := by
  have hkey := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun t => -(Real.log t)⁻¹)
    (fun x hx => hasDerivAt_negInvLog (le_trans ha (Set.mem_Ici.mp hx)))
    (fun x hx => by
      have hx2 : (0:ℝ) < x := by have := Set.mem_Ioi.mp hx; linarith
      positivity)
    tendsto_negInvLog
  simpa using hkey

/-! ## Integrability of the `E`-part integrand `hInt` -/

/-- `hInt` is integrable on the compact `[2, x]`.  It equals the corpus-integrable
`−(mF'·Sfun) − (t log t)⁻¹`, whose pieces are individually integrable. -/
theorem integrableOn_hInt_Icc {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn hInt (Set.Icc 2 x) := by
  have h1 : IntegrableOn (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      (Set.Icc 2 x) :=
    integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF_real hx)
  have h2 : IntegrableOn (fun t => (t * Real.log t)⁻¹) (Set.Icc 2 x) := by
    have hc : ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.Icc 2 x) := by
      have := continuousOn_inv_tlog_real (a := 2) (b := x) le_rfl hx
      rwa [Set.uIcc_of_le hx] at this
    exact hc.integrableOn_compact isCompact_Icc
  have hsub : IntegrableOn (fun t => -(deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      - (t * Real.log t)⁻¹) (Set.Icc 2 x) := h1.neg.sub h2
  refine hsub.congr_fun (fun t ht => ?_) measurableSet_Icc
  simp only [Set.mem_Icc] at ht
  have ht2 : (2:ℝ) ≤ t := ht.1
  have ht0 : (0:ℝ) < t := by linarith
  have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  change -(deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k) - (t * Real.log t)⁻¹
      = (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹
  rw [deriv_mF ht2, show Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k from rfl]
  field_simp

/-- `hInt` is interval-integrable on `[2, x]`. -/
theorem intervalIntegrable_hInt {x : ℝ} (hx : 2 ≤ x) : IntervalIntegrable hInt volume 2 x :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (integrableOn_hInt_Icc hx)

/-- The dominating pointwise bound: `|hInt t| ≤ 6 (t log²t)⁻¹` for `t ≥ 2`. -/
theorem norm_hInt_le {t : ℝ} (ht : 2 ≤ t) : ‖hInt t‖ ≤ 6 * (t * Real.log t ^ 2)⁻¹ := by
  have hinvnn : (0:ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by
    have ht0 : (0:ℝ) < t := by linarith
    positivity
  have hE : |Sfun t - Real.log t| ≤ 6 := abs_Sfun_sub_log_le ht
  rw [hInt, Real.norm_eq_abs, abs_mul, abs_of_nonneg hinvnn]
  exact mul_le_mul_of_nonneg_right hE hinvnn

/-- The `[2,x]` norm-integral of `hInt` is bounded by `6/log 2`, uniformly in `x`. -/
theorem integral_norm_hInt_le {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, ‖hInt t‖ ≤ 6 * (Real.log 2)⁻¹ := by
  have hstep : ∫ t in (2:ℝ)..x, ‖hInt t‖
      ≤ ∫ t in (2:ℝ)..x, 6 * (t * Real.log t ^ 2)⁻¹ := by
    apply intervalIntegral.integral_mono_on hx
    · exact (intervalIntegrable_hInt hx).norm
    · exact ((continuousOn_inv_tlogsq_real le_rfl hx).intervalIntegrable).const_mul 6
    · intro t ht
      simp only [Set.mem_Icc] at ht
      exact norm_hInt_le ht.1
  have heval : ∫ t in (2:ℝ)..x, 6 * (t * Real.log t ^ 2)⁻¹
      = 6 * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_tlogsq_real le_rfl hx]
  rw [heval] at hstep
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have : (0:ℝ) ≤ (Real.log x)⁻¹ := by positivity
  nlinarith [hstep]

/-- **`hInt` is integrable on `(2, ∞)`.**  The improper integral defining the
Mertens constant converges absolutely. -/
theorem integrableOn_hInt_Ioi : IntegrableOn hInt (Set.Ioi 2) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (6 * (Real.log 2)⁻¹) 2
    (b := fun n : ℕ => (n:ℝ) + 2)
    (fun n => (intervalIntegrable_hInt (le_add_of_nonneg_left (Nat.cast_nonneg n))).1)
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    (Filter.Eventually.of_forall
      (fun n => integral_norm_hInt_le (le_add_of_nonneg_left (Nat.cast_nonneg n))))

/-! ## The Abel identity, tail split, and assembly -/

/-- **The Abel identity for `Σ_{p≤x} 1/p`, decomposed.**  For `x ≥ 2`,
`Σ_{p≤x} 1/p = 1 + E(x)/log x + (log log x − log log 2) + ∫₂ˣ E/(t log²t)`,
where `E = Sfun − log`.  This is Abel summation with the `log`-part integrated
explicitly and the `E`-part left as `∫ hInt`. -/
theorem sum_inv_eq {x : ℝ} (hx : 2 ≤ x) :
    ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mF k * mC k
      = 1 + (Sfun x - Real.log x) * (Real.log x)⁻¹
        + (Real.log (Real.log x) - Real.log (Real.log 2)) + ∫ t in (2:ℝ)..x, hInt t := by
  have hlogxne : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have habel := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one x
    (fun t ht => differentiableAt_mF (by simp only [Set.mem_Icc] at ht; exact ht.1))
    (integrableOn_deriv_mF_real hx)
  rw [← intervalIntegral.integral_of_le hx] at habel
  -- boundary term
  have hbdry : mF x * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mC k)
      = 1 + (Sfun x - Real.log x) * (Real.log x)⁻¹ := by
    rw [show (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, mC k) = Sfun x from rfl, mF]
    field_simp
    ring
  -- integral term
  have hIInf : IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) volume 2 x :=
    ((continuousOn_inv_tlog_real le_rfl hx).intervalIntegrable).neg
  have hintterm : (∫ t in (2:ℝ)..x, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = -(Real.log (Real.log x) - Real.log (Real.log 2)) - ∫ t in (2:ℝ)..x, hInt t := by
    have hcongr : (∫ t in (2:ℝ)..x, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
        = ∫ t in (2:ℝ)..x, (-(t * Real.log t)⁻¹ - hInt t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have ht2 : (2:ℝ) ≤ t := ht.1
      have ht0 : (0:ℝ) < t := by linarith
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      change deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k
          = -(t * Real.log t)⁻¹ - (Sfun t - Real.log t) * (t * Real.log t ^ 2)⁻¹
      rw [deriv_mF ht2, show Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k from rfl]
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_sub hIInf (intervalIntegrable_hInt hx),
      intervalIntegral.integral_neg, integral_inv_tlog_real le_rfl hx]
  rw [hbdry, hintterm] at habel
  rw [habel]; ring

/-- The interval integral `∫₂ˣ hInt` equals the improper tail split
`(∫_{Ioi 2} hInt) − (∫_{Ioi x} hInt)` for `x ≥ 2`. -/
theorem interval_eq_Ioi_sub {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2:ℝ)..x, hInt t
      = (∫ t in Set.Ioi (2:ℝ), hInt t) - ∫ t in Set.Ioi x, hInt t := by
  have hI2 : IntegrableOn hInt (Set.Ioi 2) := integrableOn_hInt_Ioi
  have hIoc : IntegrableOn hInt (Set.Ioc 2 x) := hI2.mono_set Set.Ioc_subset_Ioi_self
  have hIoix : IntegrableOn hInt (Set.Ioi x) := hI2.mono_set (Set.Ioi_subset_Ioi hx)
  have hunion : ∫ t in Set.Ioi (2:ℝ), hInt t
      = (∫ t in Set.Ioc 2 x, hInt t) + ∫ t in Set.Ioi x, hInt t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoix
  rw [intervalIntegral.integral_of_le hx, hunion]; ring

/-- **Tail bound.** `|∫_{Ioi x} hInt| ≤ 6/log x` for `x ≥ 2` — the improper
integral's tail, dominated by `6·∫ₓ^∞ (t log²t)⁻¹ = 6/log x`. -/
theorem abs_tail_le {x : ℝ} (hx : 2 ≤ x) :
    |∫ t in Set.Ioi x, hInt t| ≤ 6 * (Real.log x)⁻¹ := by
  have hIoix : IntegrableOn hInt (Set.Ioi x) :=
    integrableOn_hInt_Ioi.mono_set (Set.Ioi_subset_Ioi hx)
  have hdomint : IntegrableOn (fun t => 6 * (t * Real.log t ^ 2)⁻¹) (Set.Ioi x) :=
    (integrableOn_invtlogsq_Ioi hx).const_mul 6
  calc |∫ t in Set.Ioi x, hInt t|
      = ‖∫ t in Set.Ioi x, hInt t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Set.Ioi x, ‖hInt t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi x, 6 * (t * Real.log t ^ 2)⁻¹ := by
        refine setIntegral_mono_on hIoix.norm hdomint measurableSet_Ioi (fun t ht => ?_)
        exact norm_hInt_le (le_of_lt (lt_of_le_of_lt hx (Set.mem_Ioi.mp ht)))
    _ = 6 * ∫ t in Set.Ioi x, (t * Real.log t ^ 2)⁻¹ := integral_const_mul _ _
    _ = 6 * (Real.log x)⁻¹ := by rw [integral_invtlogsq_Ioi hx]

/-- **The sharp Mertens second theorem.**  There is a constant `M` (the
Meissel–Mertens constant, identified as `γ − B` only downstream) with
`|Σ_{p≤n} 1/p − (log log n + M)| ≤ 12 / log n` for all `n ≥ 2`. -/
theorem mertens_second_sharp :
    ∃ M : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p)
        - (Real.log (Real.log n) + M)| ≤ C / Real.log n := by
  refine ⟨1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2:ℝ), hInt t, 12, by norm_num, ?_⟩
  intro n hn
  have hx : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlogx : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hinvnn : (0:ℝ) ≤ (Real.log (n:ℝ))⁻¹ := le_of_lt (by positivity)
  -- rewrite the prime sum as the Abel value, then decompose it
  have hLHS : (∑ p ∈ (Finset.range (n+1)).filter Nat.Prime, (1:ℝ)/p)
      = ∑ k ∈ Finset.Icc 0 ⌊(n:ℝ)⌋₊, mF k * mC k := by
    rw [sum_mF_mul_mC_eq (n:ℝ), Nat.floor_natCast]
  rw [hLHS, sum_inv_eq hx]
  -- collapse the difference to `E(n)/log n − ∫_{Ioi n} hInt`
  have hdiff : 1 + (Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
        + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log 2))
        + (∫ t in (2:ℝ)..(n:ℝ), hInt t)
        - (Real.log (Real.log (n:ℝ))
            + (1 - Real.log (Real.log 2) + ∫ t in Set.Ioi (2:ℝ), hInt t))
      = (Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
          - ∫ t in Set.Ioi (n:ℝ), hInt t := by
    rw [interval_eq_Ioi_sub hx]; ring
  rw [hdiff]
  -- triangle inequality + the two `≤ 6/log n` bounds
  have hb1 : |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹|
      ≤ 6 * (Real.log (n:ℝ))⁻¹ := by
    rw [abs_mul, abs_of_nonneg hinvnn]
    exact mul_le_mul_of_nonneg_right (abs_Sfun_sub_log_le hx) hinvnn
  have hb2 : |∫ t in Set.Ioi (n:ℝ), hInt t| ≤ 6 * (Real.log (n:ℝ))⁻¹ := abs_tail_le hx
  calc |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹
          - ∫ t in Set.Ioi (n:ℝ), hInt t|
      ≤ |(Sfun (n:ℝ) - Real.log (n:ℝ)) * (Real.log (n:ℝ))⁻¹|
          + |∫ t in Set.Ioi (n:ℝ), hInt t| := by
        rw [sub_eq_add_neg, ← abs_neg (∫ t in Set.Ioi (n:ℝ), hInt t)]
        exact abs_add_le _ _
    _ ≤ 6 * (Real.log (n:ℝ))⁻¹ + 6 * (Real.log (n:ℝ))⁻¹ := by linarith [hb1, hb2]
    _ = 12 / Real.log (n:ℝ) := by rw [div_eq_mul_inv]; ring

end Salt.Mertens

-- ==== upstream: Salt/MR/TuranKubilius.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# The Turán–Kubilius inequality (MR-gate node S6b, `= MR-C`)

The variance of `ω(n) = n.primeFactors.card` over `n ≤ x` is `≪ x · loglog x`.
Elementary and self-contained modulo `Salt.Mertens.mertens_second_sharp`.

## Domain note (statement defect flagged, not silently patched)

The frozen target used the hypothesis `2 ≤ x`.  That literal statement is
**false**: for `2 ≤ x < e` we have `Real.log (Real.log x) < 0`, so the RHS
`C · x · loglog x` is negative while the LHS is a sum of squares `≥ 0`.
Concretely at `x = 2` the LHS is `≈ 2.0016 > 0 > RHS` for every `C > 0`.
The faithful theorem (the classical "for all sufficiently large `x`" form) is
landed here with an existential threshold `x₀`; the shape
`variance ≤ C · x · loglog x` is preserved exactly.  A Fable/human-tier
statement fix of the freeze is required before this node can be "landed" under
the literal `2 ≤ x` hypothesis.
-/

namespace Salt.MR

open Finset

/-- Primes `≤ N`, indexed so its reciprocal sum matches `mertens_second_sharp`. -/
def primesLE (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- `∑_{p ≤ N} 1/p`, the Mertens partial sum. -/
noncomputable def primeRecip (N : ℕ) : ℝ := ∑ p ∈ primesLE N, (1 : ℝ) / p

lemma mem_primesLE {N p : ℕ} : p ∈ primesLE N ↔ p ≤ N ∧ p.Prime := by
  simp [primesLE, Finset.mem_filter, Finset.mem_range]

lemma primeRecip_nonneg (N : ℕ) : 0 ≤ primeRecip N := by
  refine Finset.sum_nonneg ?_
  intro p _; positivity

/-- `Finset.Icc 1 N = Finset.Ioc 0 N` over `ℕ`. -/
lemma Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- Counting multiples of `d` in `[1, N]`. -/
lemma card_Icc_filter_dvd (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  rw [Icc_one_eq_Ioc_zero]; exact Nat.Ioc_filter_dvd_card_eq_div N d

/-- Lower bound on nat-division cast to `ℝ`: `N/p - 1 ≤ ⌊N/p⌋`. -/
lemma cast_div_ge {N p : ℕ} (hp : 0 < p) : (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hmod : ((N % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt N hp
  have hdm : (p : ℝ) * ((N / p : ℕ) : ℝ) + ((N % p : ℕ) : ℝ) = (N : ℝ) := by
    exact_mod_cast Nat.div_add_mod N p
  rw [sub_le_iff_le_add, div_le_iff₀ hp']
  nlinarith [hdm, hmod]

/-- For `n ∈ [1, N]`, `n.primeFactors` are exactly the primes `≤ N` dividing `n`. -/
lemma primeFactors_eq_filter {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    n.primeFactors = (primesLE N).filter (fun p => p ∣ n) := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, mem_primesLE]
  constructor
  · rintro ⟨hp, hpn, _⟩
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    exact ⟨⟨by omega, hp⟩, hpn⟩
  · rintro ⟨⟨_, hp⟩, hpn⟩
    exact ⟨hp, hpn, by omega⟩

/-- `ω(n)` as an indicator sum over primes `≤ N`, for `n ∈ [1, N]`. -/
lemma omega_eq_sum {N n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    ((n.primeFactors.card : ℝ))
      = ∑ p ∈ primesLE N, (if p ∣ n then (1 : ℝ) else 0) := by
  rw [primeFactors_eq_filter hn1 hnN, Finset.card_filter]
  push_cast
  rfl

/-- The first moment `∑_{n ≤ N} ω(n) = ∑_{p ≤ N} ⌊N/p⌋`. -/
lemma first_moment (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ))
      = ∑ p ∈ primesLE N, ((N / p : ℕ) : ℝ) := by
  rw [Finset.sum_congr rfl
      (fun n hn => omega_eq_sum (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_boole, card_Icc_filter_dvd]

/-- `#{primes ≤ N} ≤ N`. -/
lemma card_primesLE_le (N : ℕ) : ((primesLE N).card : ℝ) ≤ N := by
  have hsub : primesLE N ⊆ Finset.Icc 2 N := by
    intro p hp
    obtain ⟨hpN, hp⟩ := mem_primesLE.1 hp
    exact Finset.mem_Icc.2 ⟨hp.two_le, hpN⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  have : (primesLE N).card ≤ N := by omega
  exact_mod_cast this

/-- Upper bound on the first moment: `∑ ω(n) ≤ N · ∑ 1/p`. -/
lemma first_moment_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ≤ (N : ℝ) * primeRecip N := by
  rw [first_moment, primeRecip, Finset.mul_sum]
  refine Finset.sum_le_sum (fun p _ => ?_)
  calc ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
    _ = (N : ℝ) * (1 / p) := by rw [mul_one_div]

/-- Lower bound on the first moment: `N · ∑ 1/p - N ≤ ∑ ω(n)`. -/
lemma first_moment_ge (N : ℕ) :
    (N : ℝ) * primeRecip N - N ≤ ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) := by
  rw [first_moment]
  have hstep : ∑ p ∈ primesLE N, ((N : ℝ) / p - 1)
      ≤ ∑ p ∈ primesLE N, ((N / p : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    exact cast_div_ge (mem_primesLE.1 hp).2.pos
  refine le_trans ?_ hstep
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hNP : (N : ℝ) * primeRecip N = ∑ p ∈ primesLE N, (N : ℝ) / p := by
    rw [primeRecip, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_); rw [mul_one_div]
  rw [hNP]
  have hc := card_primesLE_le N
  linarith

/-- Product of two divisibility indicators is the joint indicator. -/
lemma indicator_mul (p q n : ℕ) :
    (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
      = if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0 := by
  by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]

/-- `∑_{n ≤ N} 𝟙[d ∣ n] = ⌊N/d⌋`. -/
lemma sum_indicator_dvd (N d : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then (1 : ℝ) else 0) = ((N / d : ℕ) : ℝ) := by
  rw [Finset.sum_boole, card_Icc_filter_dvd]

/-- For coprime `p, q`: `∑_{n ≤ N} 𝟙[p ∣ n ∧ q ∣ n] = ⌊N/(pq)⌋`. -/
lemma sum_indicator_both (N p q : ℕ) (hcop : Nat.Coprime p q) :
    ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      = ((N / (p * q) : ℕ) : ℝ) := by
  have hcongr : ∀ n, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      = (if p * q ∣ n then (1 : ℝ) else 0) := by
    intro n
    have hiff : (p ∣ n ∧ q ∣ n) ↔ (p * q ∣ n) := by
      constructor
      · rintro ⟨h1, h2⟩; exact hcop.mul_dvd_of_dvd_of_dvd h1 h2
      · intro h; exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
    exact if_congr hiff rfl rfl
  rw [Finset.sum_congr rfl (fun n _ => hcongr n), Finset.sum_boole, card_Icc_filter_dvd]

/-- **The second moment bound.** `∑_{n ≤ N} ω(n)² ≤ N·P + N·P²`, `P = ∑_{p ≤ N} 1/p`.
The diagonal `p = q` contributes `≤ N·P`; the off-diagonal `p ≠ q` maps to `pq ∣ n`
and contributes `≤ N·P²`. -/
lemma second_moment_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2
      ≤ (N : ℝ) * primeRecip N + (N : ℝ) * (primeRecip N) ^ 2 := by
  have hsq : ∀ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2
      = ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    rw [omega_eq_sum hn1 hnN, pow_two, Finset.sum_mul_sum]
  have hcomm : (∑ n ∈ Finset.Icc 1 N, ∑ p ∈ primesLE N, ∑ q ∈ primesLE N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0))
      = ∑ p ∈ primesLE N, ∑ q ∈ primesLE N, ∑ n ∈ Finset.Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hsq, hcomm]
  have hbound : ∀ p ∈ primesLE N,
      (∑ q ∈ primesLE N, ∑ n ∈ Finset.Icc 1 N,
        (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0))
      ≤ (N : ℝ) / p * (1 + primeRecip N) := by
    intro p hp
    obtain ⟨hpN, hpp⟩ := mem_primesLE.1 hp
    have hinner : ∀ q, ∑ n ∈ Finset.Icc 1 N,
          (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0)
        = ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) :=
      fun q => Finset.sum_congr rfl (fun n _ => indicator_mul p q n)
    rw [Finset.sum_congr rfl (fun q _ => hinner q)]
    rw [← Finset.add_sum_erase (primesLE N) _ hp]
    have hdiag : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0)
        ≤ (N : ℝ) / p := by
      have hself : ∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0)
          = ∑ n ∈ Finset.Icc 1 N, (if p ∣ n then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun n _ => by simp only [and_self])
      rw [hself, sum_indicator_dvd]; exact Nat.cast_div_le
    have hoff : ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
          (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
        ≤ ∑ q ∈ primesLE N, (N : ℝ) / (p * q) := by
      have h1 : ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
            (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
          ≤ ∑ q ∈ (primesLE N).erase p, (N : ℝ) / (p * q) := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hqmem := Finset.mem_of_mem_erase hq
        have hqne : q ≠ p := Finset.ne_of_mem_erase hq
        obtain ⟨hqN, hqp⟩ := mem_primesLE.1 hqmem
        have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqp).2 hqne.symm
        rw [sum_indicator_both N p q hcop]
        exact le_trans Nat.cast_div_le (le_of_eq (by rw [Nat.cast_mul]))
      have h2 : ∑ q ∈ (primesLE N).erase p, (N : ℝ) / (p * q)
          ≤ ∑ q ∈ primesLE N, (N : ℝ) / (p * q) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p (primesLE N))
          (fun q _ _ => by positivity)
      exact h1.trans h2
    have hfactor : ∑ q ∈ primesLE N, (N : ℝ) / (p * q) = (N : ℝ) / p * primeRecip N := by
      rw [primeRecip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [mul_one_div, div_div]
    calc (∑ n ∈ Finset.Icc 1 N, (if p ∣ n ∧ p ∣ n then (1 : ℝ) else 0))
          + ∑ q ∈ (primesLE N).erase p, ∑ n ∈ Finset.Icc 1 N,
              (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
        ≤ (N : ℝ) / p + ∑ q ∈ primesLE N, (N : ℝ) / (p * q) := add_le_add hdiag hoff
      _ = (N : ℝ) / p + (N : ℝ) / p * primeRecip N := by rw [hfactor]
      _ = (N : ℝ) / p * (1 + primeRecip N) := by ring
  have heq : ∑ p ∈ primesLE N, (N : ℝ) / p * (1 + primeRecip N)
      = (N : ℝ) * primeRecip N + (N : ℝ) * (primeRecip N) ^ 2 := by
    have hNP : ∑ p ∈ primesLE N, (N : ℝ) / p = (N : ℝ) * primeRecip N := by
      rw [primeRecip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_); rw [mul_one_div]
    rw [← Finset.sum_mul, hNP]; ring
  exact (Finset.sum_le_sum hbound).trans (le_of_eq heq)

/-- **The variance bound (combinatorial heart).** For `μ ≥ 0`,
`∑_{n ≤ N} (ω(n) − μ)² ≤ N·((P − μ)² + P + 2μ)`, with `P = ∑_{p ≤ N} 1/p`.
Expand the square, apply the first/second moment estimates; the `N·μ²` terms
cancel, leaving the `O(N·μ)` shape. -/
lemma variance_bound (N : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) :
    ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      ≤ (N : ℝ) * ((primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ) := by
  have hid : ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      = (∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)) ^ 2)
        - 2 * μ * (∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ)))
        + (N : ℝ) * μ ^ 2 := by
    have hpt : ∀ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
        = ((n.primeFactors.card : ℝ)) ^ 2 - 2 * μ * ((n.primeFactors.card : ℝ)) + μ ^ 2 :=
      fun n _ => by ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 N).card : ℝ) = (N : ℝ) := by rw [Nat.card_Icc]; push_cast; ring
    rw [hcard]
  rw [hid]
  have hS2 := second_moment_le N
  have hS1l := first_moment_ge N
  nlinarith [hS2, hS1l, hμ, mul_nonneg hμ (sub_nonneg.mpr hS1l)]

/-- Bridge between `loglog N` and `loglog x` when `N ≤ x ≤ N + 1`: the gap is `≤ 1`. -/
lemma loglog_gap {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hxN : (N : ℝ) ≤ x) (hxN1 : x ≤ (N : ℝ) + 1) :
    |Real.log (Real.log (N : ℝ)) - Real.log (Real.log x)| ≤ 1 := by
  have hNge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) < N := by linarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hxpos : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlo : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hxN)
  have hlogx_le : Real.log x ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hxpos hxN1
  have hlogNb : 0 < Real.log ((N : ℝ) + 1) := lt_of_lt_of_le hlogx hlogx_le
  have hba : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log (N : ℝ) := by
    have hle : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) * (N : ℝ)) :=
      Real.log_le_log (by linarith) (by nlinarith [hNge2, sq_nonneg ((N : ℝ) - 2)])
    rw [Real.log_mul (ne_of_gt hNpos) (ne_of_gt hNpos)] at hle
    linarith
  have hup : Real.log (Real.log x) ≤ Real.log (Real.log (N : ℝ)) + 1 := by
    have hstep : Real.log (Real.log x) ≤ Real.log (Real.log ((N : ℝ) + 1)) :=
      Real.log_le_log hlogx hlogx_le
    have hstep2 : Real.log (Real.log ((N : ℝ) + 1)) - Real.log (Real.log (N : ℝ))
        ≤ Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) - 1 := by
      rw [← Real.log_div (ne_of_gt hlogNb) (ne_of_gt hlogN)]
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hstep3 : Real.log ((N : ℝ) + 1) / Real.log (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hlogN]; linarith [hba]
    linarith [hstep, hstep2, hstep3]
  rw [abs_le]
  constructor <;> linarith [hlo, hup]

/-- **The Turán–Kubilius inequality.** The variance of `ω(n) = n.primeFactors.card`
about its mean `loglog x` is `≪ x · loglog x`.  See the domain note at the top of the
file: the frozen `2 ≤ x` hypothesis is false (negative RHS on `[2, e)`); this is the
faithful "for all sufficiently large `x`" form (existential threshold `x₀`). -/
theorem turan_kubilius :
    ∃ C : ℝ, ∃ x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.primeFactors.card : ℝ) - Real.log (Real.log x)) ^ 2
        ≤ C * x * Real.log (Real.log x) := by
  obtain ⟨M, CM, hCM, hmert⟩ := Salt.Mertens.mertens_second_sharp
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := |M| + CM / Real.log 2 + 1 with hKdef
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) ≤ |M| := abs_nonneg M
    have h2 : (0 : ℝ) ≤ CM / Real.log 2 := div_nonneg hCM hlog2pos.le
    rw [hKdef]; linarith
  set L : ℝ := K ^ 2 + K with hLdef
  have hLpos : 0 ≤ L := by rw [hLdef]; nlinarith [hKpos]
  refine ⟨4, Real.exp (Real.exp L), by norm_num, ?_⟩
  intro x hx
  have hx0pos : (0 : ℝ) < Real.exp (Real.exp L) := Real.exp_pos _
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hx0pos hx
  have hx2 : (2 : ℝ) ≤ x := by
    have he1 : (1 : ℝ) ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
    have hmono : Real.exp 1 ≤ Real.exp (Real.exp L) := Real.exp_le_exp.mpr he1
    have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  set N := ⌊x⌋₊ with hNdef
  have hN2 : 2 ≤ N := by rw [hNdef]; exact Nat.le_floor (by exact_mod_cast hx2)
  have hNge2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNx : (N : ℝ) ≤ x := by rw [hNdef]; exact Nat.floor_le hxpos.le
  have hxN1 : x ≤ (N : ℝ) + 1 := by rw [hNdef]; exact (Nat.lt_floor_add_one x).le
  set μ := Real.log (Real.log x) with hμdef
  have hlogx_ge : Real.exp L ≤ Real.log x := by
    have h := Real.log_le_log hx0pos hx; rwa [Real.log_exp] at h
  have hμL : L ≤ μ := by
    rw [hμdef]; have h := Real.log_le_log (Real.exp_pos L) hlogx_ge; rwa [Real.log_exp] at h
  have hμ0 : 0 ≤ μ := le_trans hLpos hμL
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith [hNge2R])
  have hmertN : |primeRecip N - (Real.log (Real.log (N : ℝ)) + M)|
      ≤ CM / Real.log (N : ℝ) := by
    have h := hmert N hN2
    simpa [primeRecip, primesLE] using h
  have hgap : |Real.log (Real.log (N : ℝ)) - μ| ≤ 1 := by
    rw [hμdef]; exact loglog_gap hN2 hNx hxN1
  have hCMbound : CM / Real.log (N : ℝ) ≤ CM / Real.log 2 := by
    rw [div_le_div_iff₀ hlogNpos hlog2pos]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hNge2R) hCM
  have hPmu : |primeRecip N - μ| ≤ K := by
    calc |primeRecip N - μ|
        ≤ |primeRecip N - (Real.log (Real.log (N : ℝ)) + M)|
          + |(Real.log (Real.log (N : ℝ)) + M) - μ| := abs_sub_le _ _ _
      _ ≤ CM / Real.log (N : ℝ) + (|M| + |Real.log (Real.log (N : ℝ)) - μ|) := by
          have hb2 : |(Real.log (Real.log (N : ℝ)) + M) - μ|
              ≤ |M| + |Real.log (Real.log (N : ℝ)) - μ| := by
            have heq : (Real.log (Real.log (N : ℝ)) + M) - μ
                = M + (Real.log (Real.log (N : ℝ)) - μ) := by ring
            rw [heq]; exact abs_add_le M _
          linarith [hmertN, hb2]
      _ ≤ CM / Real.log 2 + (|M| + 1) := by linarith [hCMbound, hgap]
      _ = K := by rw [hKdef]; ring
  have hvar := variance_bound N μ hμ0
  have hsq : (primeRecip N - μ) ^ 2 ≤ K ^ 2 :=
    sq_le_sq' (abs_le.mp hPmu).1 (abs_le.mp hPmu).2
  have hPle : primeRecip N ≤ μ + K := by have := (abs_le.mp hPmu).2; linarith
  have hbracket : (primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ ≤ 4 * μ := by
    have hL : K ^ 2 + K ≤ μ := by rw [← hLdef]; exact hμL
    nlinarith [hsq, hPle, hL]
  calc ∑ n ∈ Finset.Icc 1 N, ((n.primeFactors.card : ℝ) - μ) ^ 2
      ≤ (N : ℝ) * ((primeRecip N - μ) ^ 2 + primeRecip N + 2 * μ) := hvar
    _ ≤ (N : ℝ) * (4 * μ) := by
        exact mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ ≤ x * (4 * μ) := by
        exact mul_le_mul_of_nonneg_right hNx (by linarith [hμ0])
    _ = 4 * x * μ := by ring

end Salt.MR



theorem solution :
    ∃ C : ℝ, ∃ x₀ : ℝ, 0 < C ∧ ∀ x : ℝ, x₀ ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((n.primeFactors.card : ℝ) - Real.log (Real.log x)) ^ 2
        ≤ C * x * Real.log (Real.log x) :=
  Salt.MR.turan_kubilius
