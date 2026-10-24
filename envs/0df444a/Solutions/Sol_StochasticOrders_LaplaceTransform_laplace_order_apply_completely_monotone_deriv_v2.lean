-- Prove2me | solution 1 for StochasticOrders.LaplaceTransform.laplace_order_apply_completely_monotone_deriv_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T21:17:09.952376+00:00
-- url     : https://prove2.me/submissions/8d6381c9-9973-4519-8efe-a9417cda4b2c

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone_v2

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace CPL97LT

theorem cm_taylor (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (b y : ℝ) (hyb : y < b) (n : ℕ) :
    ∃ η ∈ Set.Ioo y b, φ y =
      (∑ k ∈ Finset.range (n + 1), (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial) +
        (-1) ^ (n + 1) * iteratedDeriv (n + 1) φ η * (η - y) ^ n / n.factorial * (b - y) := by
  have hne : b ≠ y := hyb.ne'
  have hu : UniqueDiffOn ℝ (Set.uIcc b y) := uniqueDiffOn_uIcc hne
  have hCD : ∀ m : ℕ, ContDiff ℝ m φ := fun m => contDiff_infty.mp hφ m
  have hcd : ContDiffOn ℝ (n + 1 : ℕ) φ (Set.uIcc b y) := (hCD (n + 1)).contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n φ (Set.uIcc b y)) (Set.uIoo b y) :=
    (hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hu).mono
      Set.Ioo_subset_Icc_self
  obtain ⟨η, hη, h⟩ := taylor_mean_remainder_cauchy hne (hCD n).contDiffOn hdiff
  have hη' : η ∈ Set.Ioo y b := by
    simpa [Set.uIoo, min_eq_right hyb.le, max_eq_left hyb.le] using hη
  refine ⟨η, hη', ?_⟩
  have hbmem : b ∈ Set.uIcc b y := Set.left_mem_uIcc
  have hηmem : η ∈ Set.uIcc b y := by
    rw [Set.uIcc_of_ge hyb.le]; exact Set.Ioo_subset_Icc_self hη'
  rw [taylor_within_apply,
    iteratedDerivWithin_eq_iteratedDeriv hu ((hCD (n + 1)).contDiffAt) hηmem] at h
  have hsum : ∀ k ∈ Finset.range (n + 1),
      ((k.factorial : ℝ)⁻¹ * (y - b) ^ k) • iteratedDerivWithin k φ (Set.uIcc b y) b =
        (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial := by
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hCD k).contDiffAt) hbmem, smul_eq_mul]
    have : (y - b) ^ k = (-1) ^ k * (b - y) ^ k := by rw [← mul_pow]; ring
    rw [this, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hsum] at h
  have h2 : (y - η) ^ n = (-1) ^ n * (η - y) ^ n := by rw [← mul_pow]; ring
  rw [h2, sub_eq_iff_eq_add] at h
  rw [h, pow_succ]
  ring

/-- the Taylor coefficient weights -/
theorem cm_partial_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 ≤ y) (hyb : y < b) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial
      ≤ φ y := by
  obtain ⟨η, hη, h⟩ := cm_taylor φ hφ b y hyb n
  rw [h]
  have hη0 : 0 < η := lt_of_le_of_lt hy hη.1
  have := hsign (n + 1) η hη0
  have h1 : 0 ≤ (η - y) ^ n := pow_nonneg (by linarith [hη.1]) n
  have h2 : 0 ≤ (b - y) := by linarith
  have h3 : 0 ≤ (-1) ^ (n + 1) * iteratedDeriv (n + 1) φ η * (η - y) ^ n / n.factorial * (b - y) :=
    mul_nonneg (div_nonneg (mul_nonneg this h1) (Nat.cast_nonneg _)) h2
  linarith

theorem cm_term_nonneg (φ : ℝ → ℝ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hb : 0 < b) (hyb : y ≤ b) (k : ℕ) :
    0 ≤ (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial :=
  div_nonneg (mul_nonneg (hsign k b hb) (pow_nonneg (by linarith) k)) (Nat.cast_nonneg _)

theorem cm_single_le (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 ≤ y) (hyb : y < b) (m : ℕ) :
    (-1) ^ m * iteratedDeriv m φ b * (b - y) ^ m / m.factorial ≤ φ y := by
  refine le_trans ?_ (cm_partial_le φ hφ hsign b y hy hyb m)
  exact Finset.single_le_sum (f := fun k => (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k /
    k.factorial) (fun k _ => cm_term_nonneg φ hsign b y (by linarith) hyb.le k)
    (Finset.self_mem_range_succ m)

theorem cm_rem_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 < y) (hyb : y < b) (n : ℕ) :
    φ y - ∑ k ∈ Finset.range (n + 1), (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial
      ≤ φ 0 * ((b - y) / y) * ((n + 1) * (1 - y / b) ^ n) := by
  obtain ⟨η, hη, h⟩ := cm_taylor φ hφ b y hyb n
  have hη0 : 0 < η := lt_trans hy hη.1
  set A := (-1) ^ (n + 1) * iteratedDeriv (n + 1) φ η with hA
  have hA0 : 0 ≤ A := hsign (n + 1) η hη0
  have hsingle := cm_single_le φ hφ hsign η 0 le_rfl hη0 (n + 1)
  rw [← hA, sub_zero] at hsingle
  -- hsingle : A * η ^ (n+1) / (n+1)! ≤ φ 0
  have hrem : φ y - ∑ k ∈ Finset.range (n + 1),
      (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial =
      A * (η - y) ^ n / n.factorial * (b - y) := by
    rw [h]; ring
  rw [hrem]
  have hfac : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [hfac] at hsingle
  -- A * η^(n+1) ≤ φ 0 * (n+1) * n!
  have hA' : A * η ^ (n + 1) ≤ φ 0 * ((n + 1) * n.factorial) := by
    rwa [div_le_iff₀ (by positivity)] at hsingle
  set r := (η - y) / η with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith [hη.1]) hη0.le
  have hrq : r ≤ 1 - y / b := by
    rw [hr, div_le_iff₀ hη0, sub_mul, one_mul, div_mul_eq_mul_div]
    have : y * η / b ≤ y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [hη.2]
    linarith
  have hpow : (η - y) ^ n = r ^ n * η ^ n := by
    rw [hr, div_pow, div_mul_cancel₀]; exact pow_ne_zero _ hη0.ne'
  rw [hpow]
  have hq0 : 0 ≤ 1 - y / b := le_trans hr0 hrq
  have hrn : r ^ n ≤ (1 - y / b) ^ n := pow_le_pow_left₀ hr0 hrq n
  have hφ0 : 0 ≤ φ 0 := by
    have h0 := mul_nonneg hA0 (pow_nonneg hη0.le (n + 1))
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) * n.factorial := by positivity
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    linarith
  -- A * η^n ≤ φ0 * (n+1) * n! / η
  have hAη : A * η ^ n ≤ φ 0 * ((n + 1) * n.factorial) / η := by
    rw [le_div_iff₀ hη0, mul_assoc, ← pow_succ]; exact hA'
  have hby : 0 ≤ b - y := by linarith
  calc A * (r ^ n * η ^ n) / n.factorial * (b - y)
      = (A * η ^ n) * r ^ n * (b - y) / n.factorial := by ring
    _ ≤ (φ 0 * ((n + 1) * n.factorial) / η) * (1 - y / b) ^ n * (b - y) / n.factorial := by
        gcongr
    _ = φ 0 * (b - y) / η * ((n + 1) * (1 - y / b) ^ n) := by
        field_simp
    _ ≤ φ 0 * (b - y) / y * ((n + 1) * (1 - y / b) ^ n) := by
        gcongr
        exact hη.1.le
    _ = φ 0 * ((b - y) / y) * ((n + 1) * (1 - y / b) ^ n) := by ring

/-- Bernstein weights: `w_k(b) = (-1)^k φ^{(k)}(b) b^k / k!`. -/
noncomputable def cmW (φ : ℝ → ℝ) (b : ℝ) (k : ℕ) : ℝ :=
  (-1) ^ k * iteratedDeriv k φ b * b ^ k / k.factorial

/-- The exponential-sum approximant `ψ_b(y) = ∑ w_k(b) e^{-(k/b) y}`. -/
noncomputable def cmPsi (φ : ℝ → ℝ) (b y : ℝ) : ℝ :=
  ∑' k : ℕ, cmW φ b k * Real.exp (-((k : ℝ) / b * y))

theorem cmW_nonneg (φ : ℝ → ℝ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) (k : ℕ) : 0 ≤ cmW φ b k :=
  div_nonneg (mul_nonneg (hsign k b hb) (pow_nonneg hb.le k)) (Nat.cast_nonneg _)

theorem cmW_term (φ : ℝ → ℝ) (b y : ℝ) (hb : 0 < b) (k : ℕ) :
    cmW φ b k * (1 - y / b) ^ k = (-1) ^ k * iteratedDeriv k φ b * (b - y) ^ k / k.factorial := by
  have : b - y = b * (1 - y / b) := by field_simp
  rw [cmW, this, mul_pow]
  ring

theorem cm_exp_le_one (s x : ℝ) (hs : 0 ≤ s) (hx : 0 ≤ x) : Real.exp (-(s * x)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have := mul_nonneg hs hx
  linarith

theorem cmW_summable (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) : Summable (cmW φ b) ∧ ∑' k, cmW φ b k ≤ φ 0 := by
  have hpart : ∀ n, ∑ i ∈ Finset.range n, cmW φ b i ≤ φ 0 := by
    intro n
    have h1 := cm_partial_le φ hφ hsign b 0 le_rfl hb n
    have h2 : ∑ i ∈ Finset.range (n + 1), cmW φ b i =
        ∑ k ∈ Finset.range (n + 1), (-1) ^ k * iteratedDeriv k φ b * (b - 0) ^ k /
          k.factorial := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_zero, cmW]
    have h3 : ∑ i ∈ Finset.range n, cmW φ b i ≤ ∑ i ∈ Finset.range (n + 1), cmW φ b i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ n))
        (fun i _ _ => cmW_nonneg φ hsign b hb i)
    linarith
  exact ⟨summable_of_sum_range_le (cmW_nonneg φ hsign b hb) hpart,
    Real.tsum_le_of_sum_range_le (cmW_nonneg φ hsign b hb) hpart⟩

theorem cm_hasSum_pos (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 < y) (hyb : y < b) :
    HasSum (fun k => cmW φ b k * (1 - y / b) ^ k) (φ y) := by
  have hb : 0 < b := lt_trans hy hyb
  have hq0 : 0 ≤ 1 - y / b := by
    rw [sub_nonneg, div_le_one hb]; exact hyb.le
  have hq1 : 1 - y / b < 1 := by
    have : 0 < y / b := div_pos hy hb
    linarith
  have hnn : ∀ k, 0 ≤ cmW φ b k * (1 - y / b) ^ k :=
    fun k => mul_nonneg (cmW_nonneg φ hsign b hb k) (pow_nonneg hq0 k)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [cmW_term φ b y hb]
  set C := φ 0 * ((b - y) / y)
  have hε : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * (1 - y / b) ^ n)) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have h3 := (h1.add h2).const_mul C
    simp only [add_zero, mul_zero] at h3
    refine h3.congr fun n => ?_
    ring
  have hlow : Tendsto (fun n : ℕ => φ y - C * (((n : ℝ) + 1) * (1 - y / b) ^ n)) atTop
      (𝓝 (φ y)) := by
    simpa using (tendsto_const_nhds (x := φ y)).sub hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have := cm_rem_bound φ hφ hsign b y hy hyb n
    simp only
    linarith
  · exact cm_partial_le φ hφ hsign b y hy.le hyb n

theorem cm_tsum_eq (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) : ∑' k, cmW φ b k = φ 0 := by
  obtain ⟨hs, hle⟩ := cmW_summable φ hφ hsign b hb
  refine le_antisymm hle ?_
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), φ y ≤ ∑' k, cmW φ b k := by
    filter_upwards [Ioo_mem_nhdsGT hb] with y hy
    have h1 := cm_hasSum_pos φ hφ hsign b y hy.1 hy.2
    have hq0 : 0 ≤ 1 - y / b := by
      rw [sub_nonneg, div_le_one hb]; exact hy.2.le
    have hq1 : 1 - y / b ≤ 1 := by
      have : 0 ≤ y / b := div_nonneg hy.1.le hb.le
      linarith
    refine hasSum_le (fun k => ?_) h1 hs.hasSum
    exact mul_le_of_le_one_right (cmW_nonneg φ hsign b hb k) (pow_le_one₀ hq0 hq1)
  have hc : Tendsto φ (𝓝[>] (0 : ℝ)) (𝓝 (φ 0)) :=
    hφ.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hc hev

theorem cm_hasSum (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 ≤ y) (hyb : y < b) :
    HasSum (fun k => cmW φ b k * (1 - y / b) ^ k) (φ y) := by
  rcases hy.lt_or_eq with hy | rfl
  · exact cm_hasSum_pos φ hφ hsign b y hy hyb
  · have hb : 0 < b := hyb
    simp only [zero_div, sub_zero, one_pow, mul_one]
    rw [← cm_tsum_eq φ hφ hsign b hb]
    exact (cmW_summable φ hφ hsign b hb).1.hasSum

theorem cm_pow_sub_le (u v : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (m : ℕ) :
    u ^ (m + 1) - v ^ (m + 1) ≤ ((m : ℝ) + 1) * u ^ m * (u - v) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hu : 0 ≤ u := le_trans hv hvu
    have h1 : v ^ (m + 1) ≤ u ^ (m + 1) := pow_le_pow_left₀ hv hvu _
    have h2 : 0 ≤ u - v := by linarith
    calc u ^ (m + 1 + 1) - v ^ (m + 1 + 1)
        = u * (u ^ (m + 1) - v ^ (m + 1)) + v ^ (m + 1) * (u - v) := by ring
      _ ≤ u * (((m : ℝ) + 1) * u ^ m * (u - v)) + u ^ (m + 1) * (u - v) :=
          add_le_add (mul_le_mul_of_nonneg_left ih hu) (mul_le_mul_of_nonneg_right h1 h2)
      _ = (((m + 1 : ℕ) : ℝ) + 1) * u ^ (m + 1) * (u - v) := by push_cast; ring

theorem cm_exp_sub_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    0 ≤ Real.exp (-((k : ℝ) * t)) - (1 - t) ^ k ∧
      Real.exp (-((k : ℝ) * t)) - (1 - t) ^ k ≤ 2 * t := by
  have hv : 0 ≤ 1 - t := by linarith
  have hvu : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t); linarith
  have hpow : ∀ j : ℕ, Real.exp (-((j : ℝ) * t)) = Real.exp (-t) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]; ring_nf
  constructor
  · rw [hpow k, sub_nonneg]
    exact pow_le_pow_left₀ hv hvu k
  · cases k with
    | zero => simp; linarith
    | succ m =>
      rw [hpow (m + 1)]
      have h1 := cm_pow_sub_le (Real.exp (-t)) (1 - t) hv hvu m
      have h2 : Real.exp (-t) - (1 - t) ≤ t ^ 2 := by
        have := Real.abs_exp_sub_one_sub_id_le (x := -t) (by rw [abs_neg, abs_of_nonneg ht0]; exact ht1)
        have h' := (abs_le.mp this).2
        nlinarith
      set E := Real.exp (-t) ^ m with hE
      have hE0 : 0 ≤ E := pow_nonneg (Real.exp_pos _).le m
      have hE1 : E ≤ 1 := pow_le_one₀ (Real.exp_pos _).le (by
        rw [Real.exp_le_one_iff]; linarith)
      have hmE : (m : ℝ) * t * E ≤ 1 := by
        rw [hE, ← hpow m]
        have h3 := Real.add_one_le_exp ((m : ℝ) * t)
        have h4 : Real.exp ((m : ℝ) * t) * Real.exp (-((m : ℝ) * t)) = 1 := by
          rw [← Real.exp_add]; simp
        have h5 : 0 < Real.exp (-((m : ℝ) * t)) := Real.exp_pos _
        nlinarith
      have htE : t * E ≤ 1 := by nlinarith
      have hd0 : 0 ≤ Real.exp (-t) - (1 - t) := by linarith
      calc Real.exp (-t) ^ (m + 1) - (1 - t) ^ (m + 1)
          ≤ ((m : ℝ) + 1) * E * (Real.exp (-t) - (1 - t)) := h1
        _ ≤ ((m : ℝ) + 1) * E * t ^ 2 := by
            apply mul_le_mul_of_nonneg_left h2; positivity
        _ = t * ((m : ℝ) * t * E) + t * (t * E) := by ring
        _ ≤ t * 1 + t * 1 := by gcongr
        _ = 2 * t := by ring

theorem cm_psi_summable (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) :
    Summable (fun k : ℕ => cmW φ b k * Real.exp (-((k : ℝ) / b * y))) :=
  Summable.of_nonneg_of_le
    (fun k => mul_nonneg (cmW_nonneg φ hsign b hb k) (Real.exp_pos _).le)
    (fun k => mul_le_of_le_one_right (cmW_nonneg φ hsign b hb k)
      (cm_exp_le_one _ _ (by positivity) hy))
    (cmW_summable φ hφ hsign b hb).1

theorem cm_psi_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hb : 0 < b) (hy : 0 ≤ y) : 0 ≤ cmPsi φ b y ∧ cmPsi φ b y ≤ φ 0 := by
  constructor
  · exact tsum_nonneg fun k => mul_nonneg (cmW_nonneg φ hsign b hb k) (Real.exp_pos _).le
  · rw [← cm_tsum_eq φ hφ hsign b hb]
    refine hasSum_le (fun k => ?_) (cm_psi_summable φ hφ hsign b y hb hy).hasSum
      (cmW_summable φ hφ hsign b hb).1.hasSum
    exact mul_le_of_le_one_right (cmW_nonneg φ hsign b hb k)
      (cm_exp_le_one _ _ (by positivity) hy)

theorem cm_psi_approx (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b y : ℝ) (hy : 0 ≤ y) (hyb : y < b) :
    |cmPsi φ b y - φ y| ≤ 2 * (y / b) * φ 0 := by
  have hb : 0 < b := lt_of_le_of_lt hy hyb
  set t := y / b with ht
  have ht0 : 0 ≤ t := div_nonneg hy hb.le
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hb]; exact hyb.le
  have hA := (cm_psi_summable φ hφ hsign b y hb hy).hasSum
  have hB := cm_hasSum φ hφ hsign b y hy hyb
  have hD := hA.sub hB
  have hexp : ∀ k : ℕ, Real.exp (-((k : ℝ) / b * y)) = Real.exp (-((k : ℝ) * t)) := by
    intro k; rw [ht]; ring_nf
  have hW := (cmW_summable φ hφ hsign b hb).1.hasSum.mul_left (2 * t)
  rw [cm_tsum_eq φ hφ hsign b hb] at hW
  have h0 : 0 ≤ cmPsi φ b y - φ y := by
    refine hasSum_le (fun k => ?_) hasSum_zero hD
    simp only [hexp]
    rw [← mul_sub]
    exact mul_nonneg (cmW_nonneg φ hsign b hb k) (cm_exp_sub_le t ht0 ht1 k).1
  have h1 : cmPsi φ b y - φ y ≤ 2 * t * φ 0 := by
    refine hasSum_le (fun k => ?_) hD hW
    simp only [hexp]
    rw [← mul_sub]
    have := mul_le_mul_of_nonneg_left (cm_exp_sub_le t ht0 ht1 k).2 (cmW_nonneg φ hsign b hb k)
    linarith
  rw [abs_of_nonneg h0]
  exact h1

theorem cm_psi_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (y : ℝ) (hy : 0 ≤ y) :
    Tendsto (fun m : ℕ => cmPsi φ ((m : ℝ) + 1) y) atTop (𝓝 (φ y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun m : ℕ => 2 * y * φ 0 * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * y * φ 0)
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_ hlim
  rw [Filter.eventually_atTop]
  refine ⟨⌈y⌉₊, fun m hm => ?_⟩
  have hym : y < (m : ℝ) + 1 := by
    have : y ≤ (m : ℝ) := le_trans (Nat.le_ceil y) (by exact_mod_cast hm)
    linarith
  rw [Real.norm_eq_abs]
  refine le_trans (cm_psi_approx φ hφ hsign ((m : ℝ) + 1) y hy hym) (le_of_eq ?_)
  ring

theorem cm_int_hasSum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) :
    HasSum (fun k : ℕ => ∫ ω, cmW φ b k * Real.exp (-((k : ℝ) / b * X ω)) ∂μ)
      (∫ ω, cmPsi φ b (X ω) ∂μ) := by
  refine hasSum_integral_of_dominated_convergence (fun k _ => cmW φ b k) ?_ ?_ ?_ ?_ ?_
  · intro k
    exact (by fun_prop : Measurable fun ω => cmW φ b k *
      Real.exp (-((k : ℝ) / b * X ω))).aestronglyMeasurable
  · intro k
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cmW_nonneg φ hsign b hb k)
      (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (cmW_nonneg φ hsign b hb k)
      (cm_exp_le_one _ _ (by positivity) (hXnn ω))
  · exact Eventually.of_forall fun ω => (cmW_summable φ hφ hsign b hb).1
  · exact integrable_const _
  · exact Eventually.of_forall fun ω => (cm_psi_summable φ hφ hsign b (X ω) hb (hXnn ω)).hasSum

theorem cm_psi_aesm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fun ω => cmPsi φ b (X ω)) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n ω => ∑ k ∈ Finset.range n, cmW φ b k * Real.exp (-((k : ℝ) / b * X ω)))
    (fun n => ?_) (Eventually.of_forall fun ω => ?_)
  · exact (by fun_prop : Measurable fun ω => ∑ k ∈ Finset.range n,
      cmW φ b k * Real.exp (-((k : ℝ) / b * X ω))).aestronglyMeasurable
  · exact (cm_psi_summable φ hφ hsign b (X ω) hb (hXnn ω)).hasSum.tendsto_sum_nat

theorem cm_dct {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x) :
    Tendsto (fun m : ℕ => ∫ ω, cmPsi φ ((m : ℝ) + 1) (X ω) ∂μ) atTop
      (𝓝 (∫ ω, φ (X ω) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => φ 0)
    (fun m => cm_psi_aesm μ X hX hXnn φ hφ hsign ((m : ℝ) + 1) (by positivity))
    (integrable_const _) (fun m => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => cm_psi_tendsto φ hφ hsign (X ω) (hXnn ω))
  obtain ⟨h0, h1⟩ := cm_psi_bound φ hφ hsign ((m : ℝ) + 1) (X ω) (by positivity) (hXnn ω)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

open StochasticOrders.LaplaceTransform in
theorem cm_int_compare {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (b : ℝ) (hb : 0 < b) (h : LaplaceOrder μ ν X Y) :
    ∫ ω, cmPsi φ b (Y ω) ∂ν ≤ ∫ ω, cmPsi φ b (X ω) ∂μ := by
  refine hasSum_le (fun k => ?_) (cm_int_hasSum ν Y hY hYnn φ hφ hsign b hb)
    (cm_int_hasSum μ X hX hXnn φ hφ hsign b hb)
  rw [integral_const_mul, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (cmW_nonneg φ hsign b hb k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact h ((k : ℝ) / b) (by positivity)


theorem comp_sign (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0))
    (hg' : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (deriv g) x) :
    ∀ n : ℕ, ∀ c : ℝ, 0 ≤ c → ∀ x : ℝ, 0 < x →
      0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (fun y => c * Real.exp (-(s * g y))) x := by
  have hop : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hgd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv g) (Set.Ioi 0) :=
    hg.deriv_of_isOpen hop (by simp)
  have hF : ∀ c : ℝ, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => c * Real.exp (-(s * g y))) (Set.Ioi 0) :=
    fun c => contDiffOn_const.mul (Real.contDiff_exp.comp_contDiffOn
      ((contDiffOn_const.mul hg).neg))
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc x hx
  rcases n with _ | n
  · simp only [pow_zero, one_mul, iteratedDeriv_zero]; positivity
  have hloc : deriv (fun y => c * Real.exp (-(s * g y))) =ᶠ[𝓝 x]
      fun y => -(deriv g y * ((c * s) * Real.exp (-(s * g y)))) := by
    filter_upwards [hop.mem_nhds hx] with y hy
    have hdg : HasDerivAt g (deriv g y) y :=
      ((hg.differentiableOn (by simp)).differentiableAt (hop.mem_nhds hy)).hasDerivAt
    have := ((hdg.const_mul s).fun_neg.exp).const_mul c
    rw [this.deriv]; ring
  rw [iteratedDeriv_succ', hloc.iteratedDeriv_eq, iteratedDeriv_fun_neg,
    iteratedDeriv_fun_mul ((hgd.contDiffAt (hop.mem_nhds hx)).of_le (by exact_mod_cast le_top))
      (((hF (c * s)).contDiffAt (hop.mem_nhds hx)).of_le (by exact_mod_cast le_top)),
    ← Finset.sum_neg_distrib, Finset.mul_sum]
  have key : ∀ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n + 1) * -((n.choose i : ℝ) *
      iteratedDeriv i (deriv g) x *
        iteratedDeriv (n - i) (fun y => c * s * Real.exp (-(s * g y))) x) =
      (n.choose i : ℝ) * ((-1) ^ i * iteratedDeriv i (deriv g) x) *
        ((-1) ^ (n - i) * iteratedDeriv (n - i) (fun y => c * s * Real.exp (-(s * g y))) x) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : (-1 : ℝ) ^ n = (-1) ^ i * (-1) ^ (n - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hi']
    rw [pow_succ, this]; ring
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hg' i x hx))
    (ih (n - i) (by omega) (c * s) (by positivity) x hx)

open StochasticOrders.LaplaceTransform in
theorem cm_compare {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsign : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n φ x)
    (h : LaplaceOrder μ ν X Y) :
    ∫ ω, φ (Y ω) ∂ν ≤ ∫ ω, φ (X ω) ∂μ :=
  le_of_tendsto_of_tendsto' (cm_dct ν Y hY hYnn φ hφ hsign) (cm_dct μ X hX hXnn φ hφ hsign)
    (fun m => cm_int_compare μ ν X Y hX hY hXnn hYnn φ hφ hsign ((m : ℝ) + 1) (by positivity) h)

theorem cutoff_contDiff (g : ℝ → ℝ) (s ε : ℝ) (hε : 0 < ε)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.smoothTransition (4 * (x + 3 * ε / 4) / ε) *
      Real.exp (-(s * g (x + ε)))) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge (-ε) x with hx | hx
  · have hχ : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => Real.smoothTransition (4 * (x + 3 * ε / 4) / ε)) x :=
      Real.smoothTransition.contDiffAt.comp x (by fun_prop)
    have hsh : ContDiffAt ℝ (⊤ : ℕ∞) (fun x => g (x + ε)) x := by
      have : ContDiffAt ℝ (⊤ : ℕ∞) g (x + ε) :=
        hg.contDiffAt (isOpen_Ioi.mem_nhds (by simp; linarith))
      exact this.comp x (by fun_prop)
    exact hχ.mul (Real.contDiff_exp.contDiffAt.comp x ((contDiffAt_const.mul hsh).neg))
  · have : (fun x => Real.smoothTransition (4 * (x + 3 * ε / 4) / ε) *
        Real.exp (-(s * g (x + ε)))) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < -3 * ε / 4 by linarith)] with y hy
      rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
      apply div_nonpos_of_nonpos_of_nonneg _ hε.le
      simp at hy; linarith
    exact (contDiffAt_const).congr_of_eventuallyEq this

theorem cutoff_sign (g : ℝ → ℝ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0))
    (hg' : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (deriv g) x)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (fun x => Real.smoothTransition (4 * (x + 3 * ε / 4) / ε) *
      Real.exp (-(s * g (x + ε)))) x := by
  have : (fun x => Real.smoothTransition (4 * (x + 3 * ε / 4) / ε) *
        Real.exp (-(s * g (x + ε)))) =ᶠ[𝓝 x]
      fun y => 1 * Real.exp (-(s * g (y + ε))) := by
    filter_upwards [Ioi_mem_nhds (show -ε / 2 < x by linarith)] with y hy
    rw [Real.smoothTransition.one_of_one_le]
    rw [le_div_iff₀ hε]; simp at hy; linarith
  have e := iteratedDeriv_comp_add_const n (fun z => 1 * Real.exp (-(s * g z))) ε
  rw [this.iteratedDeriv_eq, e]
  exact comp_sign g s hs hg hg' n 1 zero_le_one (x + ε) (by linarith)

open StochasticOrders.LaplaceTransform in
theorem shifted {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (g : ℝ → ℝ) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0))
    (hg' : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n (deriv g) x)
    (h : LaplaceOrder μ ν X Y) :
    ∫ ω, Real.exp (-(s * g (Y ω + ε))) ∂ν ≤ ∫ ω, Real.exp (-(s * g (X ω + ε))) ∂μ := by
  have key := cm_compare μ ν X Y hX hY hXnn hYnn _ (cutoff_contDiff g s ε hε hg)
    (cutoff_sign g s ε hs hε hg hg') h
  have hone : ∀ y : ℝ, 0 ≤ y → Real.smoothTransition (4 * (y + 3 * ε / 4) / ε) = 1 := by
    intro y hy
    rw [Real.smoothTransition.one_of_one_le]
    rw [le_div_iff₀ hε]; linarith
  simp only [hone _ (hXnn _), hone _ (hYnn _), one_mul] at key
  exact key

theorem lim_shift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω) (g : ℝ → ℝ)
    (hgcont : ContinuousOn g (Set.Ici 0)) (hgpos : ∀ x, 0 ≤ x → 0 < g x) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun m : ℕ => ∫ ω, Real.exp (-(s * g (X ω + 1 / ((m : ℝ) + 1)))) ∂μ) atTop
      (𝓝 (∫ ω, Real.exp (-(s * g (X ω))) ∂μ)) := by
  set G : ℝ → ℝ := fun x => g (max x 0) with hGdef
  have hG : Continuous G :=
    hgcont.comp_continuous (continuous_id.max continuous_const) (fun x => Set.mem_Ici.2 (le_max_right x 0))
  have hGm : Measurable G := hG.measurable
  have hGe : ∀ x, 0 ≤ x → g x = G x := fun x hx => by simp [hGdef, max_eq_left hx]
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun m => ?_)
    (integrable_const _) (fun m => Eventually.of_forall fun ω => ?_)
    (Eventually.of_forall fun ω => ?_)
  · have : (fun ω => Real.exp (-(s * g (X ω + 1 / ((m : ℝ) + 1))))) =
        fun ω => Real.exp (-(s * G (X ω + 1 / ((m : ℝ) + 1)))) := by
      funext ω; rw [hGe _ (by have := hXnn ω; positivity)]
    rw [this]
    exact (by fun_prop : Measurable fun ω =>
      Real.exp (-(s * G (X ω + 1 / ((m : ℝ) + 1))))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := hgpos (X ω + 1 / ((m : ℝ) + 1)) (by have := hXnn ω; positivity)
    have := mul_pos hs this
    linarith
  · have h1 : Tendsto (fun m : ℕ => X ω + 1 / ((m : ℝ) + 1)) atTop (𝓝 (X ω + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h1
    have hc : Continuous fun x => Real.exp (-(s * G x)) := by fun_prop
    have h2 := (hc.tendsto (X ω)).comp h1
    rw [hGe _ (hXnn ω)]
    refine h2.congr fun m => ?_
    simp only [Function.comp_apply]
    rw [hGe _ (by have := hXnn ω; positivity)]

end CPL97LT

open StochasticOrders.LaplaceTransform in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (g : ℝ → ℝ)
    (hgcont : ContinuousOn g (Set.Ici 0)) (hgdiff : DifferentiableOn ℝ g (Set.Ioi 0))
    (hgpos : ∀ x, 0 ≤ x → 0 < g x) (hgderiv : CompletelyMonotone (deriv g))
    (h : LaplaceOrder μ ν X Y) :
    LaplaceOrder μ ν (g ∘ X) (g ∘ Y) := by
  obtain ⟨hgd, hg'⟩ := hgderiv
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) :=
    (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2 ⟨hgdiff, hgd⟩
  intro s hs
  simp only [Function.comp_apply, ge_iff_le]
  exact le_of_tendsto_of_tendsto' (CPL97LT.lim_shift ν Y hY hYnn g hgcont hgpos s hs)
    (CPL97LT.lim_shift μ X hX hXnn g hgcont hgpos s hs)
    (fun m => CPL97LT.shifted μ ν X Y hX hY hXnn hYnn g s (1 / ((m : ℝ) + 1)) hs
      (by positivity) hg hg' h)
